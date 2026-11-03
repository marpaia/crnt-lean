import CRNT.Persistence.ZeroSeparatingRegion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A compact zero-separating region in the plane

`exists_zsh` (`ZeroSeparatingRegion.lean`) gives half-spaces `⟨a, x⟩ ≥ b` that keep a trajectory
away from the boundary of the orthant, valid inside a box `x ≤ M`.  In two dimensions this file adds
half-spaces at infinity and obtains a **compact** region with the same validity property on every
facet:

for a facet with outward normal `n` and every `h ∈ H` with `⟨n, h⟩ > 0`, every point `x` of the
facet (in the region enlarged by `σ ∈ [0, R']`) has `⟨h, log x⟩ ≥ δ`.

## Construction at infinity

Let `T` be the set of slopes `τ_h = -h₀/h₁ ≤ 1` (`h ∈ H`, `h₁ ≠ 0`), together with `0` and `1`,
sorted as `β 0 < β 1 < ... < β (m-1) = 1`, and `θ k = (β k + β (k+1))/2`.  For a large scale `c`
the *right* family of facets is

`x₀ + β k · x₁ ≤ c + d k`,  `d 0 = 0`,  `d (k+1) = d k + (β (k+1) - β k) · c ^ θ k`,

and the *top* family is its mirror image.  On the right facet `k`, the neighbouring facets force
`c ^ θ (k-1) ≤ x₁ ≤ c ^ θ k` and `x₀ ≈ c`, so `log x ≈ log c · (1, θ)` with `θ` strictly between the
critical slopes adjacent to `β k`: every `h` with `⟨(1, β k), h⟩ > 0` has `⟨(1, θ), h⟩ > 0`.  The
last facet `x₀ + x₁ ≤ c + d (m-1)` is shared by both families.  The facets of `exists_zsh_uniform`
(for the box `x ≤ 2c`) close the region near the axes.

The normals depend only on `H`; the slack `δ` and the start point only move the offsets
(`exists_planar_region`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset Real Filter Topology

/-- Offsets of the right and top families at scale `c`. -/
noncomputable def offs (β : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => offs β c k + (β (k + 1) - β k) * c ^ ((β k + β (k + 1)) / 2)

theorem offs_succ (β : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    offs β c (k + 1) = offs β c k + (β (k + 1) - β k) * c ^ ((β k + β (k + 1)) / 2) := rfl

theorem offs_nonneg {β : ℕ → ℝ} {c : ℝ} {m : ℕ} (hc : 0 < c)
    (hβ : ∀ k, k + 1 < m → β k < β (k + 1)) : ∀ k, k < m → 0 ≤ offs β c k := by
  intro k
  induction k with
  | zero => intro _; simp [offs]
  | succ k ih =>
    intro hk
    rw [offs_succ]
    have h1 := ih (by omega)
    have h2 : 0 ≤ (β (k + 1) - β k) * c ^ ((β k + β (k + 1)) / 2) :=
      mul_nonneg (by linarith [hβ k hk]) (rpow_pos_of_pos hc _).le
    linarith

theorem offs_le {β : ℕ → ℝ} {c θM : ℝ} {m : ℕ} (hc : 1 ≤ c)
    (hβ : ∀ k, k + 1 < m → β k < β (k + 1))
    (hθ : ∀ k, k + 1 < m → (β k + β (k + 1)) / 2 ≤ θM) :
    ∀ k, k < m → offs β c k ≤ (β k - β 0) * c ^ θM := by
  intro k
  induction k with
  | zero => intro _; simp [offs]
  | succ k ih =>
    intro hk
    rw [offs_succ]
    have h1 := ih (by omega)
    have h2 : c ^ ((β k + β (k + 1)) / 2) ≤ c ^ θM := rpow_le_rpow_of_exponent_le hc (hθ k hk)
    have h3 : (β (k + 1) - β k) * c ^ ((β k + β (k + 1)) / 2) ≤ (β (k + 1) - β k) * c ^ θM :=
      mul_le_mul_of_nonneg_left h2 (by linarith [hβ k hk])
    nlinarith

/-- `h₀ log u ≥ h₀ log c - |h₀| log 2` for `u ∈ [c/2, 2c]`. -/
theorem mul_log_ge_of_mem {c u : ℝ} (hc : 0 < c) (hu1 : c / 2 ≤ u) (hu2 : u ≤ 2 * c) (h₀ : ℝ) :
    h₀ * log c - |h₀| * log 2 ≤ h₀ * log u := by
  have hl1 : log c - log 2 ≤ log u := by
    rw [← log_div hc.ne' (by norm_num)]
    exact log_le_log (by positivity) hu1
  have hl2 : log u ≤ log 2 + log c := by
    rw [← log_mul (by norm_num) hc.ne']
    exact log_le_log (by linarith) hu2
  rcases le_or_gt 0 h₀ with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_neg h]; nlinarith

/-- The margin estimate on a facet: `log x ≈ log c · (1, θ)`. -/
theorem planar_margin {c u v θ : ℝ} (hc : 0 < c) (hu1 : c / 2 ≤ u) (hu2 : u ≤ 2 * c) (hv : 0 < v)
    (h₀ h₁ : ℝ) (hlo : 0 < h₁ → c ^ θ ≤ v) (hhi : h₁ < 0 → v ≤ c ^ θ) :
    (h₀ + θ * h₁) * log c - |h₀| * log 2 ≤ h₀ * log u + h₁ * log v := by
  have h1 := mul_log_ge_of_mem hc hu1 hu2 h₀
  have h2 : h₁ * (θ * log c) ≤ h₁ * log v := by
    rcases lt_trichotomy h₁ 0 with h | h | h
    · have : log v ≤ θ * log c := by
        rw [← log_rpow hc]; exact log_le_log hv (hhi h)
      nlinarith
    · rw [h]; simp
    · have : θ * log c ≤ log v := by
        rw [← log_rpow hc]; exact log_le_log (rpow_pos_of_pos hc _) (hlo h)
      exact mul_le_mul_of_nonneg_left this h.le
  nlinarith

/-- The diagonal facet, in the half where `v ≤ u`. -/
theorem planar_diag {c u v θ δ : ℝ} (hc : 0 < c) (hu1 : c / 2 ≤ u) (hu2 : u ≤ 2 * c)
    (hv : c ^ θ ≤ v) (hvu : v ≤ u) (h₀ h₁ : ℝ) (hpos : 0 < h₀ + h₁)
    (hcrit : 0 < h₁ → 0 < h₀ + θ * h₁)
    (hG1 : δ + 2 * (|h₀| + |h₁|) ≤ (h₀ + h₁) * log c)
    (hGθ : 0 < h₀ + θ * h₁ → δ + 2 * (|h₀| + |h₁|) ≤ (h₀ + θ * h₁) * log c) :
    δ ≤ h₀ * log u + h₁ * log v := by
  have hl2 : log 2 < 2 := by
    have := log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num); linarith
  have hl20 : 0 < log 2 := log_pos (by norm_num)
  have hv0 : 0 < v := lt_of_lt_of_le (rpow_pos_of_pos hc _) hv
  rcases lt_trichotomy h₁ 0 with hneg | hzero | hposh
  · -- `h₁ < 0`: use `v ≤ u`
    have hlog : log v ≤ log u := log_le_log hv0 hvu
    have h1 := mul_log_ge_of_mem hc hu1 hu2 (h₀ + h₁)
    have e : |h₀ + h₁| ≤ |h₀| + |h₁| := abs_add_le _ _
    have : h₁ * log u ≤ h₁ * log v := by nlinarith
    have h3 : |h₀ + h₁| * log 2 ≤ 2 * (|h₀| + |h₁|) := by nlinarith [abs_nonneg (h₀ + h₁)]
    nlinarith
  · subst hzero
    have h1 := mul_log_ge_of_mem hc hu1 hu2 h₀
    simp only [add_zero, abs_zero] at hG1 hpos ⊢
    have : |h₀| * log 2 ≤ 2 * |h₀| := by nlinarith [abs_nonneg h₀]
    nlinarith
  · have hm := hcrit hposh
    have h1 := planar_margin hc hu1 hu2 hv0 h₀ h₁ (fun _ => hv) (fun h => absurd h (not_lt.mpr hposh.le))
    have h2 := hGθ hm
    have : |h₀| * log 2 ≤ 2 * (|h₀| + |h₁|) := by nlinarith [abs_nonneg h₀, abs_nonneg h₁]
    linarith

/-- Two facets `u + βj v ≤ K + oj` and `u + βk v = K + ok` with `βj < βk` and
`ok = oj + (βk - βj) t` force `t ≤ v`. -/
theorem le_of_facets {u v K oj ok βj βk t s : ℝ} (hlt : βj < βk)
    (hj : u + βj * v ≤ K + oj + s) (hk : u + βk * v = K + ok + s)
    (ho : ok = oj + (βk - βj) * t) : t ≤ v := by
  have h : (βk - βj) * t ≤ (βk - βj) * v := by nlinarith
  exact le_of_mul_le_mul_left h (by linarith)

/-- Two facets `u + βj v ≤ K + oj` and `u + βk v = K + ok` with `βk < βj` and
`oj = ok + (βj - βk) t` force `v ≤ t`. -/
theorem le_of_facets' {u v K oj ok βj βk t s : ℝ} (hlt : βk < βj)
    (hj : u + βj * v ≤ K + oj + s) (hk : u + βk * v = K + ok + s)
    (ho : oj = ok + (βj - βk) * t) : v ≤ t := by
  have h : (βj - βk) * v ≤ (βj - βk) * t := by nlinarith
  exact le_of_mul_le_mul_left h (by linarith)

/-- A coefficient bounded by `A` times a positive `v ≤ w` is bounded by `A w`. -/
theorem abs_mul_le_of {β A v w : ℝ} (hβ : |β| ≤ A) (hv : 0 < v) (hvw : v ≤ w) :
    |β * v| ≤ A * w := by
  rw [abs_mul, abs_of_pos hv]
  have h1 : |β| * v ≤ A * v := mul_le_mul_of_nonneg_right hβ hv.le
  have h2 : A * v ≤ A * w := mul_le_mul_of_nonneg_left hvw (le_trans (abs_nonneg β) hβ)
  linarith

theorem offs_eq_sum (β : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    offs β c k = ∑ j ∈ range k, (β (j + 1) - β j) * c ^ ((β j + β (j + 1)) / 2) := by
  induction k with
  | zero => simp [offs]
  | succ k ih => rw [offs_succ, ih, sum_range_succ]

theorem hasDerivAt_add_offs (β : ℕ → ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun C => C + offs β C k)
      (1 + ∑ j ∈ range k, (β (j + 1) - β j) *
        ((β j + β (j + 1)) / 2 * c ^ ((β j + β (j + 1)) / 2 - 1))) c := by
  have e : (fun C => C + offs β C k) =
      fun C => C + ∑ j ∈ range k, (β (j + 1) - β j) * C ^ ((β j + β (j + 1)) / 2) := by
    funext C; rw [offs_eq_sum]
  rw [e]
  refine (hasDerivAt_id c).add ?_
  have := HasDerivAt.sum (u := range k) (A := fun j C => (β (j + 1) - β j) *
    C ^ ((β j + β (j + 1)) / 2)) (A' := fun j => (β (j + 1) - β j) *
      ((β j + β (j + 1)) / 2 * c ^ ((β j + β (j + 1)) / 2 - 1)))
    (fun j _ => (Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul _)
  convert this using 1
  funext C
  simp

/-- For large `C` the offsets `C + offs β C k` are nondecreasing in the scale. -/
theorem exists_offs_monotone (β : ℕ → ℝ) (m : ℕ)
    (hθ : ∀ k, k + 1 < m → (β k + β (k + 1)) / 2 < 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ k, k < m → MonotoneOn (fun C => C + offs β C k) (Set.Ici C₀) := by
  set g : ℕ → ℝ := fun j => |(β (j + 1) - β j) * ((β j + β (j + 1)) / 2)| with hg
  set θ : ℕ → ℝ := fun j => (β j + β (j + 1)) / 2 with hθd
  have ht : Tendsto (fun C : ℝ => ∑ j ∈ range (m - 1), g j * C ^ (θ j - 1)) atTop (𝓝 0) := by
    have : (0 : ℝ) = ∑ j ∈ range (m - 1), g j * 0 := by simp
    rw [this]
    refine tendsto_finset_sum _ fun j hj => ?_
    have hj' : j + 1 < m := by simp at hj; omega
    have hy : 0 < 1 - θ j := by have := hθ j hj'; simp only [hθd]; linarith
    have h := (tendsto_rpow_neg_atTop hy).const_mul (g j)
    have e : -(1 - θ j) = θ j - 1 := by ring
    rw [e] at h
    exact h
  obtain ⟨C₁, hC₁⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨max C₁ 1, le_max_right _ _, fun k hk => ?_⟩
  have hpos : ∀ C ∈ Set.Ici (max C₁ 1), 0 < C := fun C hC =>
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hC)
  have hcont : ContinuousOn (fun C => C + offs β C k) (Set.Ici (max C₁ 1)) := fun C hC =>
    (hasDerivAt_add_offs β k (hpos C hC)).continuousAt.continuousWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont ?_ ?_
  · intro C hC
    rw [interior_Ici] at hC
    exact (hasDerivAt_add_offs β k (hpos C (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hC))))).differentiableAt.differentiableWithinAt
  · intro C hC
    rw [interior_Ici] at hC
    have hC0 := hpos C (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hC)))
    rw [(hasDerivAt_add_offs β k hC0).deriv]
    have hsmall := hC₁ C (le_trans (le_max_left _ _) (le_of_lt (Set.mem_Ioi.mp hC)))
    have hterm : ∀ j ∈ range k, -(g j * C ^ (θ j - 1)) ≤
        (β (j + 1) - β j) * ((β j + β (j + 1)) / 2 * C ^ ((β j + β (j + 1)) / 2 - 1)) := by
      intro j _
      have hcp : 0 < C ^ (θ j - 1) := rpow_pos_of_pos hC0 _
      have e : (β (j + 1) - β j) * ((β j + β (j + 1)) / 2 * C ^ ((β j + β (j + 1)) / 2 - 1)) =
          ((β (j + 1) - β j) * ((β j + β (j + 1)) / 2)) * C ^ (θ j - 1) := by
        simp only [hθd]; ring
      rw [e]
      have := neg_abs_le ((β (j + 1) - β j) * ((β j + β (j + 1)) / 2))
      simp only [hg]
      nlinarith
    have h1 := sum_le_sum hterm
    have h2 : ∑ j ∈ range k, g j * C ^ (θ j - 1) ≤ ∑ j ∈ range (m - 1), g j * C ^ (θ j - 1) :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun j _ _ =>
        mul_nonneg (abs_nonneg _) (rpow_pos_of_pos hC0 _).le
    rw [sum_neg_distrib] at h1
    linarith

set_option maxHeartbeats 1000000 in
/-- **A compact zero-separating region in the plane.** For a finite `H ⊆ ℝ²` closed under the
coordinate swap there are finitely many outward normals, depending only on `H`, such that for every
slack `δ` and every positive start point `x₀` suitable offsets give a region `{⟨n i, x⟩ ≤ c i}`
that contains `x₀`, lies in a box `[η, B]²` with `η > 0`, stays positive when enlarged by
`σ ≤ R'`, and on every facet of every enlargement satisfies the validity condition
`⟨n i, h⟩ > 0 → δ ≤ ⟨h, log x⟩` for `h ∈ H`. -/
theorem exists_planar_region (H : Finset (Fin 2 → ℝ))
    (hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin 2), h ∘ ρ ∈ H) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (nrm : ι → Fin 2 → ℝ),
    ∀ (δ : ℝ) (x₀ : Fin 2 → ℝ), (∀ q, 0 < x₀ q) →
    ∃ (c : ι → ℝ) (R' η B : ℝ), 0 < R' ∧ 0 < η ∧
      (∀ i, fdot (nrm i) x₀ ≤ c i) ∧
      (∀ x, (∀ i, fdot (nrm i) x ≤ c i) → ∀ q, η ≤ x q ∧ x q ≤ B) ∧
      (∀ σ, 0 ≤ σ → σ ≤ R' → ∀ x : Fin 2 → ℝ, (∀ i, fdot (nrm i) x ≤ c i + σ) →
        ∀ q, 0 < x q) ∧
      (∀ σ, 0 ≤ σ → σ ≤ R' → ∀ x : Fin 2 → ℝ, (∀ i, fdot (nrm i) x ≤ c i + σ) →
        ∀ i, fdot (nrm i) x = c i + σ →
        ∀ h ∈ H, 0 < fdot (nrm i) h → δ ≤ ∑ q, h q * log (x q)) := by
  classical
  obtain ⟨ιz, hFz, -, a, hz⟩ := exists_zsh_uniform (by norm_num : 1 ≤ 2) H hsym
  -- the slopes
  obtain ⟨T, hT⟩ : ∃ T : Finset ℝ, T = insert 0 (insert 1
      ((H.filter fun h => h 1 ≠ 0 ∧ -h 0 / h 1 ≤ 1).image fun h => -h 0 / h 1)) := ⟨_, rfl⟩
  have hT0 : (0:ℝ) ∈ T := by rw [hT]; exact mem_insert_self _ _
  have hT1 : (1:ℝ) ∈ T := by rw [hT]; exact mem_insert_of_mem (mem_insert_self _ _)
  have hTle : ∀ t ∈ T, t ≤ 1 := by
    intro t ht
    rw [hT] at ht
    simp only [mem_insert, mem_image, mem_filter] at ht
    rcases ht with rfl | rfl | ⟨h, ⟨_, _, hle⟩, rfl⟩
    · norm_num
    · exact le_rfl
    · exact hle
  have hTslope : ∀ h ∈ H, h 1 ≠ 0 → -h 0 / h 1 ≤ 1 → -h 0 / h 1 ∈ T := by
    intro h hh h1 hle
    rw [hT]
    exact mem_insert_of_mem (mem_insert_of_mem
      (mem_image.mpr ⟨h, mem_filter.mpr ⟨hh, h1, hle⟩, rfl⟩))
  obtain ⟨m, hm⟩ : ∃ m, T.card = m := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ T := by
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hT0
      · exact hT1
    have := card_le_card hsub
    rw [card_pair (by norm_num), hm] at this
    exact this
  obtain ⟨β, hβdef⟩ : ∃ β : ℕ → ℝ,
      β = fun k => if hk : k < m then T.orderEmbOfFin hm ⟨k, hk⟩ else 1 := ⟨_, rfl⟩
  have hβlt : ∀ j k, j < k → k < m → β j < β k := by
    intro j k hjk hk
    rw [hβdef]
    simp only [hk, lt_trans hjk hk, dif_pos]
    exact (T.orderEmbOfFin hm).strictMono (Fin.mk_lt_mk.mpr hjk)
  have hβle : ∀ j k, j ≤ k → k < m → β j ≤ β k := by
    intro j k hjk hk
    rcases hjk.lt_or_eq with h | rfl
    · exact (hβlt j k h hk).le
    · exact le_rfl
  have hβmem : ∀ k, k < m → β k ∈ T := by
    intro k hk
    rw [hβdef]
    simp only [dif_pos hk]
    exact T.orderEmbOfFin_mem hm _
  have hβsurj : ∀ t ∈ T, ∃ k, k < m ∧ β k = t := by
    intro t ht
    have hr := T.range_orderEmbOfFin hm
    have ht' : t ∈ Set.range (T.orderEmbOfFin hm) := by rw [hr]; exact ht
    obtain ⟨⟨k, hk⟩, hkt⟩ := ht'
    exact ⟨k, hk, by rw [hβdef]; simp only [dif_pos hk]; exact hkt⟩
  have hβlast : β (m - 1) = 1 := by
    obtain ⟨j, hj, hj1⟩ := hβsurj 1 hT1
    have h1 := hβle j (m - 1) (by omega) (by omega)
    have h2 := hTle _ (hβmem (m - 1) (by omega))
    linarith
  have hβ0 : β 0 ≤ 0 := by
    obtain ⟨j, hj, hj0⟩ := hβsurj 0 hT0
    have := hβle 0 j (Nat.zero_le _) hj
    linarith
  have hβle1 : ∀ k, k < m → β k ≤ 1 := fun k hk => hTle _ (hβmem k hk)
  have hβabs : ∀ k, k < m → |β k| ≤ |β 0| + 1 := by
    intro k hk
    have h1 := hβle 0 k (Nat.zero_le _) hk
    have h2 := hβle1 k hk
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (β 0)]
    · linarith [abs_nonneg (β 0)]
  -- transition exponents
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, θ = fun k => (β k + β (k + 1)) / 2 := ⟨_, rfl⟩
  have hθk : ∀ k, (β k + β (k + 1)) / 2 = θ k := fun k => by rw [hθdef]
  have hθlt : ∀ k, k + 1 < m → β k < θ k ∧ θ k < β (k + 1) := by
    intro k hk
    have := hβlt k (k + 1) (by omega) hk
    rw [← hθk]
    constructor <;> linarith
  obtain ⟨θM, hθM⟩ : ∃ θM, θM = θ (m - 2) := ⟨_, rfl⟩
  have hθmono : ∀ k, k + 1 < m → θ k ≤ θM := by
    intro k hk
    rw [hθM, ← hθk, ← hθk]
    have := hβle k (m - 2) (by omega) (by omega)
    have := hβle (k + 1) (m - 2 + 1) (by omega) (by omega)
    linarith
  have hθM1 : θM < 1 := by
    rw [hθM, ← hθk]
    have e : m - 2 + 1 = m - 1 := by omega
    rw [e, hβlast]
    have := hβlt (m - 2) (m - 1) (by omega) (by omega)
    rw [hβlast] at this
    linarith
  -- slope facts
  have hτ : ∀ h : Fin 2 → ℝ, h 1 ≠ 0 → h 0 = -(-h 0 / h 1) * h 1 := by
    intro h h1; field_simp
  have hS1 : ∀ h ∈ H, ∀ k, k < m → 0 < h 1 → 0 < h 0 + β k * h 1 →
      1 ≤ k ∧ 0 < h 0 + θ (k - 1) * h 1 := by
    intro h hh k hk h1 hpos
    set τ := -h 0 / h 1 with hτdef
    have e := hτ h h1.ne'
    rw [← hτdef] at e
    have hlt : τ < β k := by
      rw [e] at hpos
      have : 0 < h 1 * (β k - τ) := by nlinarith
      exact sub_pos.mp (pos_of_mul_pos_right this h1.le)
    obtain ⟨j, hj, hjτ⟩ := hβsurj τ (hTslope h hh h1.ne' (by linarith [hβle1 k hk]))
    have hjk : j < k := by
      by_contra hc
      push Not at hc
      have := hβle k j hc hj
      linarith
    refine ⟨by omega, ?_⟩
    have hj' := hβle j (k - 1) (by omega) (by omega)
    have hθ := (hθlt (k - 1) (by omega)).1
    have e2 : k - 1 + 1 = k := by omega
    rw [e]
    nlinarith
  have hS2 : ∀ h ∈ H, ∀ k, k + 1 < m → h 1 < 0 → 0 < h 0 + β k * h 1 →
      0 < h 0 + θ k * h 1 := by
    intro h hh k hk h1 hpos
    set τ := -h 0 / h 1 with hτdef
    have e := hτ h h1.ne
    rw [← hτdef] at e
    have hgt : β k < τ := by
      rw [e] at hpos
      have : 0 < h 1 * (β k - τ) := by nlinarith
      have := (pos_and_pos_or_neg_and_neg_of_mul_pos this)
      rcases this with ⟨h', _⟩ | ⟨_, h'⟩
      · linarith
      · linarith
    have hge : β (k + 1) ≤ τ := by
      by_cases hτ1 : τ ≤ 1
      · obtain ⟨j, hj, hjτ⟩ := hβsurj τ (hTslope h hh h1.ne hτ1)
        have hkj : k < j := by
          by_contra hc
          push Not at hc
          have := hβle j k hc (by omega)
          linarith
        rw [← hjτ]
        exact hβle (k + 1) j hkj hj
      · push Not at hτ1
        linarith [hβle1 (k + 1) hk]
    have hθ := (hθlt k hk).2
    rw [e]
    nlinarith
  -- the normals
  refine ⟨(Fin m × Bool) ⊕ ιz, inferInstance, ⟨Sum.inl (⟨0, by omega⟩, false)⟩,
    Sum.elim (fun p => if p.2 then ![β p.1, 1] else ![1, β p.1]) (fun j => -a j), ?_⟩
  intro δ x₀ hx₀
  -- the scale
  have hev : ∀ᶠ C in atTop, 1 ≤ C ∧ (|β 0| + 2) * (x₀ 0 + x₀ 1) ≤ C ∧ 4 ≤ C ∧
      (2 * |β 0| + 2) * C ^ (θM - 1) ≤ 1 / 4 ∧
      (∀ h ∈ H, ∀ k ∈ range (m - 1), 0 < h 0 + θ k * h 1 →
        δ + 2 * (|h 0| + |h 1|) ≤ (h 0 + θ k * h 1) * log C) ∧
      (∀ h ∈ H, 0 < h 0 + h 1 → δ + 2 * (|h 0| + |h 1|) ≤ (h 0 + h 1) * log C) := by
    refine (eventually_ge_atTop 1).and ((eventually_ge_atTop _).and
      ((eventually_ge_atTop 4).and ?_))
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
    · have ht := tendsto_rpow_neg_atTop (show 0 < 1 - θM by linarith)
      have hp : 0 < 2 * |β 0| + 2 := by positivity
      have hlim : ∀ᶠ C in atTop, C ^ (-(1 - θM)) < 1 / (4 * (2 * |β 0| + 2)) :=
        ht.eventually (gt_mem_nhds (by positivity))
      filter_upwards [hlim] with C hC
      have e : -(1 - θM) = θM - 1 := by ring
      rw [e, lt_div_iff₀ (by positivity)] at hC
      nlinarith
    · rw [eventually_all_finset]
      intro h _
      rw [eventually_all_finset]
      intro k _
      by_cases hk : 0 < h 0 + θ k * h 1
      · filter_upwards [tendsto_log_atTop.eventually_ge_atTop
          ((δ + 2 * (|h 0| + |h 1|)) / (h 0 + θ k * h 1))] with C hC _
        rw [div_le_iff₀ hk] at hC
        linarith
      · exact Filter.Eventually.of_forall fun C h' => absurd h' hk
    · rw [eventually_all_finset]
      intro h _
      by_cases hk : 0 < h 0 + h 1
      · filter_upwards [tendsto_log_atTop.eventually_ge_atTop
          ((δ + 2 * (|h 0| + |h 1|)) / (h 0 + h 1))] with C hC _
        rw [div_le_iff₀ hk] at hC
        linarith
      · exact Filter.Eventually.of_forall fun C h' => absurd h' hk
  obtain ⟨C, hC1, hC2, hC4, hC3, hG4, hG5⟩ := hev.exists
  have hC0 : 0 < C := by linarith
  have hCθ : 0 ≤ C ^ θM := (rpow_pos_of_pos hC0 _).le
  have hG3 : (2 * |β 0| + 2) * C ^ θM + 1 ≤ C / 2 := by
    have e : C ^ θM = C ^ (θM - 1) * C := by
      rw [rpow_sub_one hC0.ne']; field_simp
    rw [e]
    have : (2 * |β 0| + 2) * (C ^ (θM - 1) * C) = ((2 * |β 0| + 2) * C ^ (θM - 1)) * C := by
      ring
    rw [this]
    have h1 : ((2 * |β 0| + 2) * C ^ (θM - 1)) * C ≤ 1 / 4 * C :=
      mul_le_mul_of_nonneg_right hC3 hC0.le
    linarith
  obtain ⟨P, hP⟩ : ∃ P, P = (|β 0| + 1) * C ^ θM := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hG3' : 2 * P + 1 ≤ C / 2 := by
    have : (2 * |β 0| + 2) * C ^ θM = 2 * P := by rw [hP]; ring
    linarith
  have hoff0 : ∀ k, k < m → 0 ≤ offs β C k :=
    offs_nonneg hC0 fun k hk => hβlt k (k + 1) (by omega) hk
  have hoffle : ∀ k, k < m → offs β C k ≤ P := by
    intro k hk
    have h1 := offs_le (β := β) (m := m) hC1 (fun k hk => hβlt k (k + 1) (by omega) hk)
      (fun k hk => by rw [hθk]; exact hθmono k hk) k hk
    have h2 : β k - β 0 ≤ |β 0| + 1 := by
      have := hβle1 k hk; have := neg_abs_le (β 0); linarith
    have h3 : (β k - β 0) * C ^ θM ≤ (|β 0| + 1) * C ^ θM := mul_le_mul_of_nonneg_right h2 hCθ
    rw [hP]; linarith
  have hoffs : ∀ k, offs β C (k + 1) = offs β C k + (β (k + 1) - β k) * C ^ θ k := by
    intro k; rw [offs_succ, hθk]
  -- the offsets at infinity and near the axes
  obtain ⟨b, Rz, ηz, hRz, hηz, hstart, hfloor, hband, hvalid⟩ :=
    hz δ (2 * C) (by linarith) x₀ hx₀
  -- unpacking a point of the enlarged region
  have hfd : ∀ (u₀ u₁ : ℝ) (x : Fin 2 → ℝ), fdot ![u₀, u₁] x = u₀ * x 0 + u₁ * x 1 := by
    intro u₀ u₁ x; simp [fdot, Fin.sum_univ_two]
  have hfdneg : ∀ (j : ιz) (x : Fin 2 → ℝ), fdot (-a j) x = -fdot (a j) x := by
    intro j x; simp [fdot, sum_neg_distrib]
  have hunpack : ∀ (σ : ℝ) (x : Fin 2 → ℝ),
      (∀ i : (Fin m × Bool) ⊕ ιz, fdot (Sum.elim
        (fun p : Fin m × Bool => if p.2 then ![β p.1, 1] else ![1, β p.1])
        (fun j => -a j) i) x ≤
          Sum.elim (fun p : Fin m × Bool => C + offs β C p.1) (fun j => -b j) i + σ) →
      (∀ k, k < m → x 0 + β k * x 1 ≤ C + offs β C k + σ) ∧
      (∀ k, k < m → β k * x 0 + x 1 ≤ C + offs β C k + σ) ∧
      (∀ j, b j - σ ≤ fdot (a j) x) := by
    intro σ x hx
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun j => ?_⟩
    · have := hx (Sum.inl (⟨k, hk⟩, false))
      simpa [hfd] using this
    · have := hx (Sum.inl (⟨k, hk⟩, true))
      simpa [hfd] using this
    · have := hx (Sum.inr j)
      simp only [Sum.elim_inr, hfdneg] at this
      linarith
  have hl2 : log 2 < 2 := by
    have := log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num); linarith
  have hl20 : 0 < log 2 := log_pos (by norm_num)
  have hlog2 : ∀ g : Fin 2 → ℝ, |g 0| * log 2 ≤ 2 * (|g 0| + |g 1|) := by
    intro g
    have h1 : |g 0| * log 2 ≤ |g 0| * 2 := mul_le_mul_of_nonneg_left hl2.le (abs_nonneg _)
    linarith [abs_nonneg (g 1)]
  -- the core estimate on the right family
  have hcore : ∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ u v : ℝ, 0 < u → 0 < v →
      (∀ k, k < m → u + β k * v ≤ C + offs β C k + σ) →
      (∀ k, k < m → β k * u + v ≤ C + offs β C k + σ) →
      ∀ k, k < m → u + β k * v = C + offs β C k + σ →
      ∀ h ∈ H, 0 < h 0 + β k * h 1 → δ ≤ h 0 * log u + h 1 * log v := by
    intro σ hσ0 hσ1 u v hu hv hR hTp k hk hact h hh hpos
    by_cases hk1 : k + 1 < m
    · -- an ordinary facet
      have hvup : v ≤ C ^ θ k :=
        le_of_facets' (hβlt k (k + 1) (by omega) hk1) (hR (k + 1) hk1) hact (hoffs k)
      have hvlo : 1 ≤ k → C ^ θ (k - 1) ≤ v := by
        intro hk0
        have e : k - 1 + 1 = k := by omega
        have h2 := hoffs (k - 1)
        rw [e] at h2
        have hlt := hβlt (k - 1) k (by omega) hk
        exact le_of_facets hlt (hR (k - 1) (by omega)) hact h2
      have hθCM : C ^ θ k ≤ C ^ θM := rpow_le_rpow_of_exponent_le hC1 (hθmono k hk1)
      have hbv : |β k * v| ≤ P := by
        rw [hP]; exact abs_mul_le_of (hβabs k hk) hv (le_trans hvup hθCM)
      have hbv' := abs_le.mp hbv
      have ho1 := hoff0 k hk
      have ho2 := hoffle k hk
      have hu1 : C / 2 ≤ u := by linarith
      have hu2 : u ≤ 2 * C := by linarith
      have hfin : ∀ θ', (0 < h 1 → C ^ θ' ≤ v) → (h 1 < 0 → v ≤ C ^ θ') →
          0 < h 0 + θ' * h 1 → δ + 2 * (|h 0| + |h 1|) ≤ (h 0 + θ' * h 1) * log C →
          δ ≤ h 0 * log u + h 1 * log v := by
        intro θ' hlo hhi _ hG
        have := planar_margin hC0 hu1 hu2 hv (h 0) (h 1) hlo hhi
        have := hlog2 h
        linarith
      rcases lt_trichotomy (h 1) 0 with hneg | hzero | hposh
      · have hm' := hS2 h hh k hk1 hneg hpos
        exact hfin (θ k) (fun h' => absurd h' (not_lt.mpr hneg.le)) (fun _ => hvup) hm'
          (hG4 h hh k (mem_range.mpr (by omega)) hm')
      · have hm' : 0 < h 0 + θ k * h 1 := by rw [hzero] at hpos ⊢; simpa using hpos
        exact hfin (θ k) (fun h' => by rw [hzero] at h'; exact absurd h' (lt_irrefl 0))
          (fun h' => by rw [hzero] at h'; exact absurd h' (lt_irrefl 0)) hm'
          (hG4 h hh k (mem_range.mpr (by omega)) hm')
      · obtain ⟨hk0, hm'⟩ := hS1 h hh k hk hposh hpos
        exact hfin (θ (k - 1)) (fun _ => hvlo hk0) (fun h' => absurd h' (not_lt.mpr hposh.le))
          hm' (hG4 h hh (k - 1) (mem_range.mpr (by omega)) hm')
    · -- the diagonal facet
      have hkm : k = m - 1 := by omega
      subst hkm
      rw [hβlast] at hact hpos
      have e : m - 2 + 1 = m - 1 := by omega
      have h2 := hoffs (m - 2)
      rw [e, hβlast] at h2
      have hgap := hβlt (m - 2) (m - 1) (by omega) (by omega)
      rw [hβlast] at hgap
      have hvlo : C ^ θ (m - 2) ≤ v := le_of_facets hgap (hR (m - 2) (by omega)) hact h2
      have hulo : C ^ θ (m - 2) ≤ u := by
        have h1 := hTp (m - 2) (by omega)
        exact le_of_facets (u := v) (v := u) (K := C) (oj := offs β C (m - 2))
          (ok := offs β C (m - 1)) (s := σ) hgap (by linarith) (by linarith) h2
      have ho1 := hoff0 (m - 1) (by omega)
      have ho2 := hoffle (m - 1) (by omega)
      have hsum1 : C ≤ u + v := by linarith
      have hsum2 : u + v ≤ 2 * C := by linarith
      have hrange : m - 2 ∈ range (m - 1) := mem_range.mpr (by omega)
      have hS3 : ∀ g ∈ H, 0 < g 1 → 0 < g 0 + g 1 → 0 < g 0 + θ (m - 2) * g 1 := by
        intro g hg hg1 hgpos
        have := hS1 g hg (m - 1) (by omega) hg1 (by rw [hβlast]; linarith)
        have e' : m - 1 - 1 = m - 2 := by omega
        rw [e'] at this
        exact this.2
      rcases le_total v u with hvu | huv
      · exact planar_diag hC0 (by linarith) (by linarith) hvlo hvu (h 0) (h 1) (by linarith)
          (fun h1 => hS3 h hh h1 (by linarith)) (hG5 h hh (by linarith)) (hG4 h hh (m - 2) hrange)
      · -- the mirror half
        set g : Fin 2 → ℝ := h ∘ Equiv.swap 0 1 with hg
        have hgH : g ∈ H := hsym h hh _
        have hg0 : g 0 = h 1 := by simp [hg]
        have hg1 : g 1 = h 0 := by simp [hg]
        have hgpos : 0 < g 0 + g 1 := by rw [hg0, hg1]; linarith
        have := planar_diag hC0 (by linarith) (by linarith) hulo huv (g 0) (g 1) hgpos
          (fun h1 => hS3 g hgH h1 hgpos) (hG5 g hgH hgpos) (hG4 g hgH (m - 2) hrange)
        rw [hg0, hg1] at this
        linarith
  -- assemble
  refine ⟨Sum.elim (fun p : Fin m × Bool => C + offs β C p.1) (fun j => -b j), min Rz 1, ηz,
    2 * C, lt_min hRz one_pos, hηz, ?_, ?_, ?_, ?_⟩
  · -- the start point
    rintro (⟨k, side⟩ | j)
    · have hbx : β k * x₀ 1 ≤ (|β 0| + 1) * x₀ 1 :=
        le_trans (le_abs_self _) (by
          rw [abs_mul, abs_of_pos (hx₀ 1)]
          exact mul_le_mul_of_nonneg_right (hβabs k k.isLt) (hx₀ 1).le)
      have hbx' : β k * x₀ 0 ≤ (|β 0| + 1) * x₀ 0 :=
        le_trans (le_abs_self _) (by
          rw [abs_mul, abs_of_pos (hx₀ 0)]
          exact mul_le_mul_of_nonneg_right (hβabs k k.isLt) (hx₀ 0).le)
      have ho := hoff0 k k.isLt
      have h0 := hx₀ 0
      have h1 := hx₀ 1
      have e : (|β 0| + 2) * (x₀ 0 + x₀ 1) =
          |β 0| * x₀ 0 + |β 0| * x₀ 1 + 2 * x₀ 0 + 2 * x₀ 1 := by ring
      have e1 : (|β 0| + 1) * x₀ 1 = |β 0| * x₀ 1 + x₀ 1 := by ring
      have e0 : (|β 0| + 1) * x₀ 0 = |β 0| * x₀ 0 + x₀ 0 := by ring
      have h3 : 0 ≤ |β 0| * x₀ 0 := mul_nonneg (abs_nonneg _) h0.le
      have h4 : 0 ≤ |β 0| * x₀ 1 := mul_nonneg (abs_nonneg _) h1.le
      cases side
      · simp only [Sum.elim_inl, hfd, Bool.false_eq_true, ite_false]
        linarith
      · simp only [Sum.elim_inl, hfd, ite_true]
        linarith
    · simp only [Sum.elim_inr, hfdneg]
      linarith [hstart j]
  · -- the box
    intro x hx q
    have hx' : ∀ i : (Fin m × Bool) ⊕ ιz, fdot (Sum.elim
        (fun p : Fin m × Bool => if p.2 then ![β p.1, 1] else ![1, β p.1])
        (fun j => -a j) i) x ≤
          Sum.elim (fun p : Fin m × Bool => C + offs β C p.1) (fun j => -b j) i + 0 :=
      fun i => by rw [add_zero]; exact hx i
    obtain ⟨hR, -, hZ⟩ := hunpack 0 x hx'
    have hpos : ∀ q, 0 < x q := fun q => lt_of_lt_of_le hηz (hfloor x
      (fun j => by have := hZ j; linarith) q)
    refine ⟨hfloor x (fun j => by have := hZ j; linarith) q, ?_⟩
    have h1 := hR (m - 1) (by omega)
    rw [hβlast] at h1
    have ho := hoffle (m - 1) (by omega)
    have := hpos 0
    have := hpos 1
    fin_cases q
    · show x 0 ≤ 2 * C; linarith
    · show x 1 ≤ 2 * C; linarith
  · -- positivity in the band
    intro σ hσ0 hσ x hx q
    obtain ⟨-, -, hZ⟩ := hunpack σ x hx
    have := hband x (fun j => by have := hZ j; have := min_le_left Rz 1; linarith) q
    linarith
  · -- validity
    intro σ hσ0 hσ x hx i hact h hh hpos
    obtain ⟨hR, hTp, hZ⟩ := hunpack σ x hx
    have hσR : σ ≤ Rz := le_trans hσ (min_le_left _ _)
    have hσ1 : σ ≤ 1 := le_trans hσ (min_le_right _ _)
    have hxpos : ∀ q, 0 < x q := fun q =>
      lt_of_lt_of_le hRz (hband x (fun j => by have := hZ j; linarith) q)
    have hlog : ∑ q, h q * log (x q) = h 0 * log (x 0) + h 1 * log (x 1) := Fin.sum_univ_two _
    rcases i with ⟨k, side⟩ | j
    · cases side
      · simp only [Sum.elim_inl, hfd, Bool.false_eq_true, ite_false] at hact hpos
        rw [hlog]
        exact hcore σ hσ0 hσ1 (x 0) (x 1) (hxpos 0) (hxpos 1) hR hTp k k.isLt
          (by linarith) h hh (by linarith)
      · simp only [Sum.elim_inl, hfd, ite_true] at hact hpos
        set g : Fin 2 → ℝ := h ∘ Equiv.swap 0 1 with hg
        have hgH : g ∈ H := hsym h hh _
        have hg0 : g 0 = h 1 := by simp [hg]
        have hg1 : g 1 = h 0 := by simp [hg]
        have := hcore σ hσ0 hσ1 (x 1) (x 0) (hxpos 1) (hxpos 0)
          (fun k hk => by have := hTp k hk; linarith)
          (fun k hk => by have := hR k hk; linarith) k k.isLt (by linarith) g hgH
          (by rw [hg0, hg1]; linarith)
        rw [hg0, hg1] at this
        rw [hlog]
        linarith
    · simp only [Sum.elim_inr, hfdneg] at hact hpos
      have hxM : ∀ q, x q ≤ 2 * C := by
        have h1 := hR (m - 1) (by omega)
        rw [hβlast] at h1
        have ho := hoffle (m - 1) (by omega)
        have := hxpos 0
        have := hxpos 1
        intro q
        fin_cases q
        · show x 0 ≤ 2 * C; linarith
        · show x 1 ≤ 2 * C; linarith
      exact hvalid σ hσ0 hσR x hxpos hxM hZ j (by linarith) h hh (by linarith)


set_option maxHeartbeats 1000000 in
/-- **A compact zero-separating region in the plane.** For a finite `H ⊆ ℝ²` closed under the
coordinate swap there are finitely many outward normals, depending only on `H`, such that for every
slack `δ` and every positive start point `x₀` suitable offsets give a region `{⟨n i, x⟩ ≤ c i}`
that contains `x₀`, lies in a box `[η, B]²` with `η > 0`, stays positive when enlarged by
`σ ≤ R'`, and on every facet of every enlargement satisfies the validity condition
`⟨n i, h⟩ > 0 → δ ≤ ⟨h, log x⟩` for `h ∈ H`. -/
theorem exists_planar_infinity (H : Finset (Fin 2 → ℝ))
    (hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin 2), h ∘ ρ ∈ H) :
    ∃ (m : ℕ) (β : ℕ → ℝ), 2 ≤ m ∧ β (m - 1) = 1 ∧ (∀ k, k + 1 < m → β k < β (k + 1)) ∧
    (∀ k, k < m → |β k| ≤ |β 0| + 1) ∧ (∀ k, k + 1 < m → (β k + β (k + 1)) / 2 < 1) ∧
    ∀ δ : ℝ, ∃ C₀ : ℝ, 4 ≤ C₀ ∧ ∀ C, C₀ ≤ C →
      (∀ k, k < m → 0 ≤ offs β C k ∧ offs β C k ≤ C / 4) ∧
      (∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ u v : ℝ, 0 < u → 0 < v →
        (∀ k, k < m → u + β k * v ≤ C + offs β C k + σ) →
        (∀ k, k < m → β k * u + v ≤ C + offs β C k + σ) →
        ∀ k, k < m → u + β k * v = C + offs β C k + σ →
        ∀ h ∈ H, 0 < h 0 + β k * h 1 → δ ≤ h 0 * log u + h 1 * log v) := by
  classical
  -- the slopes
  obtain ⟨T, hT⟩ : ∃ T : Finset ℝ, T = insert 0 (insert 1
      ((H.filter fun h => h 1 ≠ 0 ∧ -h 0 / h 1 ≤ 1).image fun h => -h 0 / h 1)) := ⟨_, rfl⟩
  have hT0 : (0:ℝ) ∈ T := by rw [hT]; exact mem_insert_self _ _
  have hT1 : (1:ℝ) ∈ T := by rw [hT]; exact mem_insert_of_mem (mem_insert_self _ _)
  have hTle : ∀ t ∈ T, t ≤ 1 := by
    intro t ht
    rw [hT] at ht
    simp only [mem_insert, mem_image, mem_filter] at ht
    rcases ht with rfl | rfl | ⟨h, ⟨_, _, hle⟩, rfl⟩
    · norm_num
    · exact le_rfl
    · exact hle
  have hTslope : ∀ h ∈ H, h 1 ≠ 0 → -h 0 / h 1 ≤ 1 → -h 0 / h 1 ∈ T := by
    intro h hh h1 hle
    rw [hT]
    exact mem_insert_of_mem (mem_insert_of_mem
      (mem_image.mpr ⟨h, mem_filter.mpr ⟨hh, h1, hle⟩, rfl⟩))
  obtain ⟨m, hm⟩ : ∃ m, T.card = m := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ T := by
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hT0
      · exact hT1
    have := card_le_card hsub
    rw [card_pair (by norm_num), hm] at this
    exact this
  obtain ⟨β, hβdef⟩ : ∃ β : ℕ → ℝ,
      β = fun k => if hk : k < m then T.orderEmbOfFin hm ⟨k, hk⟩ else 1 := ⟨_, rfl⟩
  have hβlt : ∀ j k, j < k → k < m → β j < β k := by
    intro j k hjk hk
    rw [hβdef]
    simp only [hk, lt_trans hjk hk, dif_pos]
    exact (T.orderEmbOfFin hm).strictMono (Fin.mk_lt_mk.mpr hjk)
  have hβle : ∀ j k, j ≤ k → k < m → β j ≤ β k := by
    intro j k hjk hk
    rcases hjk.lt_or_eq with h | rfl
    · exact (hβlt j k h hk).le
    · exact le_rfl
  have hβmem : ∀ k, k < m → β k ∈ T := by
    intro k hk
    rw [hβdef]
    simp only [dif_pos hk]
    exact T.orderEmbOfFin_mem hm _
  have hβsurj : ∀ t ∈ T, ∃ k, k < m ∧ β k = t := by
    intro t ht
    have hr := T.range_orderEmbOfFin hm
    have ht' : t ∈ Set.range (T.orderEmbOfFin hm) := by rw [hr]; exact ht
    obtain ⟨⟨k, hk⟩, hkt⟩ := ht'
    exact ⟨k, hk, by rw [hβdef]; simp only [dif_pos hk]; exact hkt⟩
  have hβlast : β (m - 1) = 1 := by
    obtain ⟨j, hj, hj1⟩ := hβsurj 1 hT1
    have h1 := hβle j (m - 1) (by omega) (by omega)
    have h2 := hTle _ (hβmem (m - 1) (by omega))
    linarith
  have hβ0 : β 0 ≤ 0 := by
    obtain ⟨j, hj, hj0⟩ := hβsurj 0 hT0
    have := hβle 0 j (Nat.zero_le _) hj
    linarith
  have hβle1 : ∀ k, k < m → β k ≤ 1 := fun k hk => hTle _ (hβmem k hk)
  have hβabs : ∀ k, k < m → |β k| ≤ |β 0| + 1 := by
    intro k hk
    have h1 := hβle 0 k (Nat.zero_le _) hk
    have h2 := hβle1 k hk
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (β 0)]
    · linarith [abs_nonneg (β 0)]
  -- transition exponents
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, θ = fun k => (β k + β (k + 1)) / 2 := ⟨_, rfl⟩
  have hθk : ∀ k, (β k + β (k + 1)) / 2 = θ k := fun k => by rw [hθdef]
  have hθlt : ∀ k, k + 1 < m → β k < θ k ∧ θ k < β (k + 1) := by
    intro k hk
    have := hβlt k (k + 1) (by omega) hk
    rw [← hθk]
    constructor <;> linarith
  obtain ⟨θM, hθM⟩ : ∃ θM, θM = θ (m - 2) := ⟨_, rfl⟩
  have hθmono : ∀ k, k + 1 < m → θ k ≤ θM := by
    intro k hk
    rw [hθM, ← hθk, ← hθk]
    have := hβle k (m - 2) (by omega) (by omega)
    have := hβle (k + 1) (m - 2 + 1) (by omega) (by omega)
    linarith
  have hθM1 : θM < 1 := by
    rw [hθM, ← hθk]
    have e : m - 2 + 1 = m - 1 := by omega
    rw [e, hβlast]
    have := hβlt (m - 2) (m - 1) (by omega) (by omega)
    rw [hβlast] at this
    linarith
  -- slope facts
  have hτ : ∀ h : Fin 2 → ℝ, h 1 ≠ 0 → h 0 = -(-h 0 / h 1) * h 1 := by
    intro h h1; field_simp
  have hS1 : ∀ h ∈ H, ∀ k, k < m → 0 < h 1 → 0 < h 0 + β k * h 1 →
      1 ≤ k ∧ 0 < h 0 + θ (k - 1) * h 1 := by
    intro h hh k hk h1 hpos
    set τ := -h 0 / h 1 with hτdef
    have e := hτ h h1.ne'
    rw [← hτdef] at e
    have hlt : τ < β k := by
      rw [e] at hpos
      have : 0 < h 1 * (β k - τ) := by nlinarith
      exact sub_pos.mp (pos_of_mul_pos_right this h1.le)
    obtain ⟨j, hj, hjτ⟩ := hβsurj τ (hTslope h hh h1.ne' (by linarith [hβle1 k hk]))
    have hjk : j < k := by
      by_contra hc
      push Not at hc
      have := hβle k j hc hj
      linarith
    refine ⟨by omega, ?_⟩
    have hj' := hβle j (k - 1) (by omega) (by omega)
    have hθ := (hθlt (k - 1) (by omega)).1
    have e2 : k - 1 + 1 = k := by omega
    rw [e]
    nlinarith
  have hS2 : ∀ h ∈ H, ∀ k, k + 1 < m → h 1 < 0 → 0 < h 0 + β k * h 1 →
      0 < h 0 + θ k * h 1 := by
    intro h hh k hk h1 hpos
    set τ := -h 0 / h 1 with hτdef
    have e := hτ h h1.ne
    rw [← hτdef] at e
    have hgt : β k < τ := by
      rw [e] at hpos
      have : 0 < h 1 * (β k - τ) := by nlinarith
      have := (pos_and_pos_or_neg_and_neg_of_mul_pos this)
      rcases this with ⟨h', _⟩ | ⟨_, h'⟩
      · linarith
      · linarith
    have hge : β (k + 1) ≤ τ := by
      by_cases hτ1 : τ ≤ 1
      · obtain ⟨j, hj, hjτ⟩ := hβsurj τ (hTslope h hh h1.ne hτ1)
        have hkj : k < j := by
          by_contra hc
          push Not at hc
          have := hβle j k hc (by omega)
          linarith
        rw [← hjτ]
        exact hβle (k + 1) j hkj hj
      · push Not at hτ1
        linarith [hβle1 (k + 1) hk]
    have hθ := (hθlt k hk).2
    rw [e]
    nlinarith
  have hθ1 : ∀ k, k + 1 < m → (β k + β (k + 1)) / 2 < 1 := by
    intro k hk
    rw [hθk]
    have := hθmono k hk
    linarith
  refine ⟨m, β, hm2, hβlast, fun k hk => hβlt k (k + 1) (by omega) hk, hβabs, hθ1,
    fun δ => ?_⟩
  -- the scale
  have hev : ∀ᶠ C in atTop, 1 ≤ C ∧ 4 ≤ C ∧
      (2 * |β 0| + 2) * C ^ (θM - 1) ≤ 1 / 4 ∧
      (∀ h ∈ H, ∀ k ∈ range (m - 1), 0 < h 0 + θ k * h 1 →
        δ + 2 * (|h 0| + |h 1|) ≤ (h 0 + θ k * h 1) * log C) ∧
      (∀ h ∈ H, 0 < h 0 + h 1 → δ + 2 * (|h 0| + |h 1|) ≤ (h 0 + h 1) * log C) := by
    refine (eventually_ge_atTop 1).and ((eventually_ge_atTop 4).and ?_)
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
    · have ht := tendsto_rpow_neg_atTop (show 0 < 1 - θM by linarith)
      have hp : 0 < 2 * |β 0| + 2 := by positivity
      have hlim : ∀ᶠ C in atTop, C ^ (-(1 - θM)) < 1 / (4 * (2 * |β 0| + 2)) :=
        ht.eventually (gt_mem_nhds (by positivity))
      filter_upwards [hlim] with C hC
      have e : -(1 - θM) = θM - 1 := by ring
      rw [e, lt_div_iff₀ (by positivity)] at hC
      nlinarith
    · rw [eventually_all_finset]
      intro h _
      rw [eventually_all_finset]
      intro k _
      by_cases hk : 0 < h 0 + θ k * h 1
      · filter_upwards [tendsto_log_atTop.eventually_ge_atTop
          ((δ + 2 * (|h 0| + |h 1|)) / (h 0 + θ k * h 1))] with C hC _
        rw [div_le_iff₀ hk] at hC
        linarith
      · exact Filter.Eventually.of_forall fun C h' => absurd h' hk
    · rw [eventually_all_finset]
      intro h _
      by_cases hk : 0 < h 0 + h 1
      · filter_upwards [tendsto_log_atTop.eventually_ge_atTop
          ((δ + 2 * (|h 0| + |h 1|)) / (h 0 + h 1))] with C hC _
        rw [div_le_iff₀ hk] at hC
        linarith
      · exact Filter.Eventually.of_forall fun C h' => absurd h' hk
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max C₀ 4, le_max_right _ _, fun C hC => ?_⟩
  obtain ⟨hC1, hC4, hC3, hG4, hG5⟩ := hC₀ C (le_trans (le_max_left _ _) hC)
  have hC0 : 0 < C := by linarith
  have hCθ : 0 ≤ C ^ θM := (rpow_pos_of_pos hC0 _).le
  have hG3 : (2 * |β 0| + 2) * C ^ θM + 1 ≤ C / 2 := by
    have e : C ^ θM = C ^ (θM - 1) * C := by
      rw [rpow_sub_one hC0.ne']; field_simp
    rw [e]
    have : (2 * |β 0| + 2) * (C ^ (θM - 1) * C) = ((2 * |β 0| + 2) * C ^ (θM - 1)) * C := by
      ring
    rw [this]
    have h1 : ((2 * |β 0| + 2) * C ^ (θM - 1)) * C ≤ 1 / 4 * C :=
      mul_le_mul_of_nonneg_right hC3 hC0.le
    linarith
  obtain ⟨P, hP⟩ : ∃ P, P = (|β 0| + 1) * C ^ θM := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hG3' : 2 * P + 1 ≤ C / 2 := by
    have : (2 * |β 0| + 2) * C ^ θM = 2 * P := by rw [hP]; ring
    linarith
  have hoff0 : ∀ k, k < m → 0 ≤ offs β C k :=
    offs_nonneg hC0 fun k hk => hβlt k (k + 1) (by omega) hk
  have hoffle : ∀ k, k < m → offs β C k ≤ P := by
    intro k hk
    have h1 := offs_le (β := β) (m := m) hC1 (fun k hk => hβlt k (k + 1) (by omega) hk)
      (fun k hk => by rw [hθk]; exact hθmono k hk) k hk
    have h2 : β k - β 0 ≤ |β 0| + 1 := by
      have := hβle1 k hk; have := neg_abs_le (β 0); linarith
    have h3 : (β k - β 0) * C ^ θM ≤ (|β 0| + 1) * C ^ θM := mul_le_mul_of_nonneg_right h2 hCθ
    rw [hP]; linarith
  have hoffs : ∀ k, offs β C (k + 1) = offs β C k + (β (k + 1) - β k) * C ^ θ k := by
    intro k; rw [offs_succ, hθk]
  have hl2 : log 2 < 2 := by
    have := log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num); linarith
  have hl20 : 0 < log 2 := log_pos (by norm_num)
  have hlog2 : ∀ g : Fin 2 → ℝ, |g 0| * log 2 ≤ 2 * (|g 0| + |g 1|) := by
    intro g
    have h1 : |g 0| * log 2 ≤ |g 0| * 2 := mul_le_mul_of_nonneg_left hl2.le (abs_nonneg _)
    linarith [abs_nonneg (g 1)]
  -- the core estimate on the right family
  have hcore : ∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ u v : ℝ, 0 < u → 0 < v →
      (∀ k, k < m → u + β k * v ≤ C + offs β C k + σ) →
      (∀ k, k < m → β k * u + v ≤ C + offs β C k + σ) →
      ∀ k, k < m → u + β k * v = C + offs β C k + σ →
      ∀ h ∈ H, 0 < h 0 + β k * h 1 → δ ≤ h 0 * log u + h 1 * log v := by
    intro σ hσ0 hσ1 u v hu hv hR hTp k hk hact h hh hpos
    by_cases hk1 : k + 1 < m
    · -- an ordinary facet
      have hvup : v ≤ C ^ θ k :=
        le_of_facets' (hβlt k (k + 1) (by omega) hk1) (hR (k + 1) hk1) hact (hoffs k)
      have hvlo : 1 ≤ k → C ^ θ (k - 1) ≤ v := by
        intro hk0
        have e : k - 1 + 1 = k := by omega
        have h2 := hoffs (k - 1)
        rw [e] at h2
        have hlt := hβlt (k - 1) k (by omega) hk
        exact le_of_facets hlt (hR (k - 1) (by omega)) hact h2
      have hθCM : C ^ θ k ≤ C ^ θM := rpow_le_rpow_of_exponent_le hC1 (hθmono k hk1)
      have hbv : |β k * v| ≤ P := by
        rw [hP]; exact abs_mul_le_of (hβabs k hk) hv (le_trans hvup hθCM)
      have hbv' := abs_le.mp hbv
      have ho1 := hoff0 k hk
      have ho2 := hoffle k hk
      have hu1 : C / 2 ≤ u := by linarith
      have hu2 : u ≤ 2 * C := by linarith
      have hfin : ∀ θ', (0 < h 1 → C ^ θ' ≤ v) → (h 1 < 0 → v ≤ C ^ θ') →
          0 < h 0 + θ' * h 1 → δ + 2 * (|h 0| + |h 1|) ≤ (h 0 + θ' * h 1) * log C →
          δ ≤ h 0 * log u + h 1 * log v := by
        intro θ' hlo hhi _ hG
        have := planar_margin hC0 hu1 hu2 hv (h 0) (h 1) hlo hhi
        have := hlog2 h
        linarith
      rcases lt_trichotomy (h 1) 0 with hneg | hzero | hposh
      · have hm' := hS2 h hh k hk1 hneg hpos
        exact hfin (θ k) (fun h' => absurd h' (not_lt.mpr hneg.le)) (fun _ => hvup) hm'
          (hG4 h hh k (mem_range.mpr (by omega)) hm')
      · have hm' : 0 < h 0 + θ k * h 1 := by rw [hzero] at hpos ⊢; simpa using hpos
        exact hfin (θ k) (fun h' => by rw [hzero] at h'; exact absurd h' (lt_irrefl 0))
          (fun h' => by rw [hzero] at h'; exact absurd h' (lt_irrefl 0)) hm'
          (hG4 h hh k (mem_range.mpr (by omega)) hm')
      · obtain ⟨hk0, hm'⟩ := hS1 h hh k hk hposh hpos
        exact hfin (θ (k - 1)) (fun _ => hvlo hk0) (fun h' => absurd h' (not_lt.mpr hposh.le))
          hm' (hG4 h hh (k - 1) (mem_range.mpr (by omega)) hm')
    · -- the diagonal facet
      have hkm : k = m - 1 := by omega
      subst hkm
      rw [hβlast] at hact hpos
      have e : m - 2 + 1 = m - 1 := by omega
      have h2 := hoffs (m - 2)
      rw [e, hβlast] at h2
      have hgap := hβlt (m - 2) (m - 1) (by omega) (by omega)
      rw [hβlast] at hgap
      have hvlo : C ^ θ (m - 2) ≤ v := le_of_facets hgap (hR (m - 2) (by omega)) hact h2
      have hulo : C ^ θ (m - 2) ≤ u := by
        have h1 := hTp (m - 2) (by omega)
        exact le_of_facets (u := v) (v := u) (K := C) (oj := offs β C (m - 2))
          (ok := offs β C (m - 1)) (s := σ) hgap (by linarith) (by linarith) h2
      have ho1 := hoff0 (m - 1) (by omega)
      have ho2 := hoffle (m - 1) (by omega)
      have hsum1 : C ≤ u + v := by linarith
      have hsum2 : u + v ≤ 2 * C := by linarith
      have hrange : m - 2 ∈ range (m - 1) := mem_range.mpr (by omega)
      have hS3 : ∀ g ∈ H, 0 < g 1 → 0 < g 0 + g 1 → 0 < g 0 + θ (m - 2) * g 1 := by
        intro g hg hg1 hgpos
        have := hS1 g hg (m - 1) (by omega) hg1 (by rw [hβlast]; linarith)
        have e' : m - 1 - 1 = m - 2 := by omega
        rw [e'] at this
        exact this.2
      rcases le_total v u with hvu | huv
      · exact planar_diag hC0 (by linarith) (by linarith) hvlo hvu (h 0) (h 1) (by linarith)
          (fun h1 => hS3 h hh h1 (by linarith)) (hG5 h hh (by linarith)) (hG4 h hh (m - 2) hrange)
      · -- the mirror half
        set g : Fin 2 → ℝ := h ∘ Equiv.swap 0 1 with hg
        have hgH : g ∈ H := hsym h hh _
        have hg0 : g 0 = h 1 := by simp [hg]
        have hg1 : g 1 = h 0 := by simp [hg]
        have hgpos : 0 < g 0 + g 1 := by rw [hg0, hg1]; linarith
        have := planar_diag hC0 (by linarith) (by linarith) hulo huv (g 0) (g 1) hgpos
          (fun h1 => hS3 g hgH h1 hgpos) (hG5 g hgH hgpos) (hG4 g hgH (m - 2) hrange)
        rw [hg0, hg1] at this
        linarith
  exact ⟨fun k hk => ⟨hoff0 k hk, by linarith [hoffle k hk]⟩, hcore⟩

end Persistence
end CRNT
