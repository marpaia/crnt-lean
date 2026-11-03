import CRNT.Geometry.PlanarZSH
import CRNT.Geometry.PolyhedralBarrier

/-!
# Trapping by the planar zero-separating polygon

`PlanarZSH.lean` builds the polygon and shows that its edges, and a thin band inside them, sit
where a planar toric differential inclusion points inward.  This module turns that into forward
invariance of the slightly shrunk region

  `R_e = {z | ∀ j, c j + e ≤ ⟪ρ j, z⟫}`

for any curve whose velocity has nonnegative `ρ j`-component wherever the log-state is
`Good (δ / 2)` for edge `j`, on a finite time interval during which the curve stays in the box
`(0, e^{-2δ}]²`.

* `le_of_dini_slope_nonpos_in_band_le` — the band form of the Dini fencing lemma on a finite
  horizon `[0, T]` (the repository version is on `[0, ∞)`).
* `Rays.exists_band` — a uniform band width `e₀ > 0` for all edges.
* `Rays.trap` — the forward-invariance theorem.
* `Rays.exists_trapping_polygon` — everything packaged at every small scale.

Nothing here is an axiom or a `sorry`.
-/

open scoped Topology
open Filter Set

namespace CRNT
namespace PlanarZSH

/-- **Finite-horizon band fencing.**  The Dini bound is needed only on `[0, T)` and only where
`R ≤ u ≤ R'`. -/
theorem le_of_dini_slope_nonpos_in_band_le {u : ℝ → ℝ} {R R' : ℝ} (hRR' : R < R')
    (hucont : ContinuousOn u (Set.Ici 0)) (hstart : u 0 ≤ R) {T : ℝ} (hT : 0 ≤ T)
    (hdini : ∀ t, 0 ≤ t → t < T → R ≤ u t → u t ≤ R' → ∀ r : ℝ, 0 < r →
      ∀ᶠ z in 𝓝[>] t, u z < u t + r * (z - t)) :
    ∀ t, 0 ≤ t → t ≤ T → u t ≤ R := by
  have hnever : ∀ t, 0 ≤ t → t ≤ T → u t < R' := by
    intro S hS hST
    by_contra hcon
    rw [not_lt] at hcon
    set A : Set ℝ := {t ∈ Set.Ici (0 : ℝ) | R' ≤ u t} with hA
    have hAcl : IsClosed A := isClosed_Ici.isClosed_le continuousOn_const hucont
    have hAne : A.Nonempty := ⟨S, hS, hcon⟩
    have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
    set t₁ := sInf A with ht₁def
    have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
    have ht₁0 : 0 ≤ t₁ := ht₁A.1
    have ht₁S : t₁ ≤ S := csInf_le hAbdd ⟨hS, hcon⟩
    have hbefore : ∀ t, 0 ≤ t → t < t₁ → u t < R' := by
      intro t ht htlt
      by_contra hle
      rw [not_lt] at hle
      exact absurd (csInf_le hAbdd ⟨ht, hle⟩) (not_le.mpr htlt)
    have hle : u t₁ ≤ R :=
      PolyhedralBarrier.le_of_dini_slope_nonpos_at_level_le hucont hstart ht₁0
        fun t ht htlt hge r hr =>
          hdini t ht (lt_of_lt_of_le htlt (ht₁S.trans hST)) hge (hbefore t ht htlt).le r hr
    exact absurd (le_trans ht₁A.2 hle) (not_le.mpr hRR')
  intro S hS hST
  exact PolyhedralBarrier.le_of_dini_slope_nonpos_at_level_le hucont hstart hS
    fun t ht htlt hge r hr => hdini t ht (lt_of_lt_of_le htlt hST) hge
      (hnever t ht (le_of_lt (lt_of_lt_of_le htlt hST))).le r hr

/-- The linear functional `z ↦ -⟪ρ, z⟫` as a continuous linear map on `ℝ × ℝ`. -/
noncomputable def negPairCLM (ρ : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  -(ρ.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + ρ.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem negPairCLM_apply (ρ z : ℝ × ℝ) : negPairCLM ρ z = -pair ρ z := by
  simp [negPairCLM, pair]

namespace Rays

variable (F : Rays)

/-- The barrier pieces, indexed by `Fin (k+2)` (piece `i` is edge `i + 1`). -/
noncomputable def pieceL (i : Fin (F.k + 2)) : ℝ × ℝ →L[ℝ] ℝ := negPairCLM (F.ρ (i.1 + 1))

noncomputable def pieceB (c : ℕ → ℝ) (i : Fin (F.k + 2)) : ℝ := -c (i.1 + 1)

theorem piece_value (c : ℕ → ℝ) (i : Fin (F.k + 2)) (z : ℝ × ℝ) :
    F.pieceL i z - F.pieceB c i = c (i.1 + 1) - pair (F.ρ (i.1 + 1)) z := by
  simp [pieceL, pieceB, negPairCLM_apply]; ring

theorem barrier_le_iff (c : ℕ → ℝ) (e : ℝ) (z : ℝ × ℝ) :
    PolyhedralBarrier.barrier F.pieceL (F.pieceB c) z ≤ -e ↔
      ∀ j, 1 ≤ j → j ≤ F.k + 2 → c j + e ≤ pair (F.ρ j) z := by
  rw [PolyhedralBarrier.barrier_le_iff]
  constructor
  · intro h j hj1 hjk
    have := h ⟨j - 1, by omega⟩
    rw [piece_value] at this
    simp only [show j - 1 + 1 = j by omega] at this
    linarith
  · intro h i
    rw [piece_value]
    have := h (i.1 + 1) (by omega) (by omega)
    linarith

section Trap

variable {δ : ℝ} (hδ : 0 < δ) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
  (hdepth : F.D δ ≤ -Real.log b₀) (hsmall : a₀ + b₀ * (F.k * F.Q) ≤ 1)
  (hV1 : cross (F.ρ 2) (logState (a₀, b₀)) ≤ -(2 * δ * nrm (F.ρ 2)))
  (hb2δ : b₀ ≤ Real.exp (-(2 * δ)))

include hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ

/-- **A uniform band width.** -/
theorem exists_band : ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ e, 0 ≤ e → e ≤ e₀ →
    ∀ j, 1 ≤ j → j ≤ F.k + 2 → F.BandGood δ (F.off δ (a₀, b₀)) e j := by
  have hall : ∀ᶠ e in 𝓝 (0 : ℝ), ∀ j ∈ Finset.Icc 1 (F.k + 2),
      0 ≤ e → F.BandGood δ (F.off δ (a₀, b₀)) e j := by
    rw [Filter.eventually_all_finset]
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    exact F.eventually_bandGood hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ j h1 h2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε / 2, half_pos hε, fun e he0 heε j hj1 hjk => ?_⟩
  have hd : dist e 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg he0]; linarith
  exact hball hd j (Finset.mem_Icc.mpr ⟨hj1, hjk⟩) he0

/-- **Forward invariance of the shrunk region.** -/
theorem trap {e₀ : ℝ} (he₀ : ∀ e, 0 ≤ e → e ≤ e₀ →
      ∀ j, 1 ≤ j → j ≤ F.k + 2 → F.BandGood δ (F.off δ (a₀, b₀)) e j)
    {e : ℝ} (he : 0 < e) (hee₀ : e ≤ e₀)
    {γ v : ℝ → ℝ × ℝ} {T : ℝ} (hT : 0 ≤ T) (hγcont : ContinuousOn γ (Set.Ici 0))
    (hγ : ∀ t, 0 ≤ t → t < T → HasDerivAt γ (v t) t)
    (hstart : ∀ j, 1 ≤ j → j ≤ F.k + 2 → F.off δ (a₀, b₀) j + e ≤ pair (F.ρ j) (γ 0))
    (hbox : ∀ t, 0 ≤ t → t ≤ T → 0 < (γ t).1 ∧ 0 < (γ t).2 ∧
      (γ t).1 ≤ Real.exp (-(2 * δ)) ∧ (γ t).2 ≤ Real.exp (-(2 * δ)))
    (hdesc : ∀ t, 0 ≤ t → t < T → ∀ j, 1 ≤ j → j ≤ F.k + 2 →
      Good (δ / 2) (F.ρ (j - 1)) (F.ρ (j + 1)) (logState (γ t)) → 0 ≤ pair (F.ρ j) (v t)) :
    ∀ t, 0 ≤ t → t ≤ T → ∀ j, 1 ≤ j → j ≤ F.k + 2 →
      F.off δ (a₀, b₀) j + e ≤ pair (F.ρ j) (γ t) := by
  set c := F.off δ (a₀, b₀) with hc
  set u : ℝ → ℝ := fun t => PolyhedralBarrier.barrier F.pieceL (F.pieceB c) (γ t) with hu
  have hucont : ContinuousOn u (Set.Ici 0) :=
    (PolyhedralBarrier.continuous_barrier _ _).comp_continuousOn hγcont
  have hstart' : u 0 ≤ -e := (F.barrier_le_iff c e (γ 0)).mpr hstart
  have hfence := le_of_dini_slope_nonpos_in_band_le (R := -e) (R' := 0) (by linarith)
    hucont hstart' hT ?_
  · intro t ht htT
    exact (F.barrier_le_iff c e (γ t)).mp (hfence t ht htT)
  intro t ht htT hlo hhi r hr
  refine PolyhedralBarrier.eventually_barrier_lt_of_active_descent hγcont ht (hγ t ht htT) ?_ hr
  intro i hact
  -- the current band width
  set w := -u t with hw
  have hw0 : 0 ≤ w := by simp only [hw]; linarith
  have hwe : w ≤ e₀ := by simp only [hw]; linarith
  have hin : ∀ j, 1 ≤ j → j ≤ F.k + 2 → c j + w ≤ pair (F.ρ j) (γ t) :=
    (F.barrier_le_iff c w (γ t)).mp (by simp [hw, hu])
  have hjact : pair (F.ρ (i.1 + 1)) (γ t) = c (i.1 + 1) + w := by
    rw [piece_value] at hact
    simp only [hw, hu]; linarith
  obtain ⟨hp1, hp2, hb1, hb2⟩ := hbox t ht htT.le
  have hgood := he₀ w hw0 hwe (i.1 + 1) (by omega) (by omega) (γ t) hp1 hp2 hb1 hb2 hin hjact
  have := hdesc t ht htT (i.1 + 1) (by omega) (by omega) hgood
  simp only [pieceL, negPairCLM_apply]
  linarith

end Trap

/-- **The trapping polygon at every small scale.** -/
theorem exists_trapping_polygon {δ : ℝ} (hδ : 0 < δ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ K : ℕ, 1 ≤ K ∧ ∀ b₀ : ℝ, 0 < b₀ → b₀ ≤ β₀ →
      ∃ c : ℕ → ℝ, ∃ e₀ : ℝ, 0 < e₀ ∧
      (∀ j, 1 ≤ j → j ≤ F.k + 2 → 0 < c j) ∧
      (∀ z : ℝ × ℝ, b₀ ^ K ≤ z.1 → b₀ ≤ z.2 → ∀ j, 1 ≤ j → j ≤ F.k + 2 → c j ≤ pair (F.ρ j) z) ∧
      (∀ e, 0 < e → e ≤ e₀ → ∀ (γ v : ℝ → ℝ × ℝ) (T : ℝ), 0 ≤ T →
        ContinuousOn γ (Set.Ici 0) → (∀ t, 0 ≤ t → t < T → HasDerivAt γ (v t) t) →
        (∀ j, 1 ≤ j → j ≤ F.k + 2 → c j + e ≤ pair (F.ρ j) (γ 0)) →
        (∀ t, 0 ≤ t → t ≤ T → 0 < (γ t).1 ∧ 0 < (γ t).2 ∧
          (γ t).1 ≤ Real.exp (-(2 * δ)) ∧ (γ t).2 ≤ Real.exp (-(2 * δ))) →
        (∀ t, 0 ≤ t → t < T → ∀ j, 1 ≤ j → j ≤ F.k + 2 →
          Good (δ / 2) (F.ρ (j - 1)) (F.ρ (j + 1)) (logState (γ t)) → 0 ≤ pair (F.ρ j) (v t)) →
        ∀ t, 0 ≤ t → t ≤ T → ∀ j, 1 ≤ j → j ≤ F.k + 2 → c j + e ≤ pair (F.ρ j) (γ t)) := by
  -- re-derive the hypotheses of the polygon section exactly as in `exists_polygon`
  have hρ22 : 0 < (F.ρ 2).2 := by
    have := F.order 1 2 le_rfl (by norm_num) (by omega)
    simpa [cross, F.ρ1] using this
  have hN2 := F.nrm_pos 2 (by omega)
  set K : ℕ := ⌈((F.ρ 2).1 + 2 * δ * nrm (F.ρ 2)) / (F.ρ 2).2⌉₊ + 1 with hK
  have hK1 : 1 ≤ K := by omega
  have hKρ : (F.ρ 2).1 + 2 * δ * nrm (F.ρ 2) ≤ K * (F.ρ 2).2 := by
    have h := Nat.le_ceil (((F.ρ 2).1 + 2 * δ * nrm (F.ρ 2)) / (F.ρ 2).2)
    have h' : ((F.ρ 2).1 + 2 * δ * nrm (F.ρ 2)) / (F.ρ 2).2 ≤ (K : ℝ) := by
      rw [hK]; push_cast; linarith
    rwa [div_le_iff₀ hρ22] at h'
  have hkQ : 0 ≤ (F.k : ℝ) * F.Q := mul_nonneg (Nat.cast_nonneg _) F.Q_nonneg
  set β₀ : ℝ := min (min (Real.exp (-F.D δ)) (Real.exp (-(2 * δ))))
    (min (Real.exp (-1)) (1 / (1 + F.k * F.Q))) with hβ
  have hβpos : 0 < β₀ := by
    refine lt_min (lt_min (Real.exp_pos _) (Real.exp_pos _)) (lt_min (Real.exp_pos _) ?_)
    positivity
  refine ⟨β₀, hβpos, K, hK1, fun b₀ hb₀ hbβ => ?_⟩
  have hb1 : b₀ ≤ Real.exp (-F.D δ) := hbβ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hb2 : b₀ ≤ Real.exp (-(2 * δ)) :=
    hbβ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb3 : b₀ ≤ Real.exp (-1) := hbβ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb4 : b₀ ≤ 1 / (1 + F.k * F.Q) :=
    hbβ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlogle : ∀ c, b₀ ≤ Real.exp c → Real.log b₀ ≤ c := fun c h => by
    calc Real.log b₀ ≤ Real.log (Real.exp c) := Real.log_le_log hb₀ h
      _ = c := Real.log_exp c
  have hb0le1 : b₀ ≤ 1 := hb3.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have ha₀ : 0 < b₀ ^ K := pow_pos hb₀ K
  have hdepth : F.D δ ≤ -Real.log b₀ := by have := hlogle _ hb1; linarith
  have hsmall : b₀ ^ K + b₀ * (F.k * F.Q) ≤ 1 := by
    have hpow : b₀ ^ K ≤ b₀ := pow_le_of_le_one hb₀.le hb0le1 (by omega)
    have : b₀ * (1 + F.k * F.Q) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hb4; linarith
    nlinarith
  have hV1 : cross (F.ρ 2) (logState (b₀ ^ K, b₀)) ≤ -(2 * δ * nrm (F.ρ 2)) := by
    rw [cross_logState]
    simp only
    rw [Real.log_pow]
    have hL : Real.log b₀ ≤ -1 := hlogle _ hb3
    have h2δ : 0 < 2 * δ * nrm (F.ρ 2) := by positivity
    have hX : 2 * δ * nrm (F.ρ 2) ≤ K * (F.ρ 2).2 - (F.ρ 2).1 := by linarith
    have : Real.log b₀ * (K * (F.ρ 2).2 - (F.ρ 2).1) ≤ Real.log b₀ * (2 * δ * nrm (F.ρ 2)) :=
      mul_le_mul_of_nonpos_left hX (by linarith)
    nlinarith
  obtain ⟨hP0, hP1, -⟩ := F.polygon hδ ha₀ hb₀ hdepth hsmall hV1 hb2
  obtain ⟨e₀, he₀pos, he₀⟩ := F.exists_band hδ ha₀ hb₀ hdepth hsmall hV1 hb2
  refine ⟨F.off δ (b₀ ^ K, b₀), e₀, he₀pos, hP0, fun z h1 h2 => hP1 z h1 h2, ?_⟩
  intro e he hee₀ γ v T hT hγcont hγ hstart hbox hdesc
  exact F.trap hδ ha₀ hb₀ hdepth hsmall hV1 hb2 he₀ he hee₀ hT hγcont hγ hstart hbox hdesc

end Rays

end PlanarZSH
end CRNT
