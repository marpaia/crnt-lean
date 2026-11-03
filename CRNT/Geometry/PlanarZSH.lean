import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.IntermediateValue

/-!
# The planar zero-separating polygon

The transversal geometry of a codimension-two face is planar: the two transversal coordinates
`z = (a, b)` are small and positive, and the relevant log-state is
`U(z) = (-log a, -log b)`, deep in the positive quadrant.  A toric differential inclusion in the
plane is described by finitely many rays `ρ 1 = e₁, ρ 2, …, ρ (k+1), ρ (k+2) = e₂` of the closed
positive quadrant, ordered counterclockwise.  This module builds Craciun's planar
zero-separating polygon for such a fan (v3 §5) in a form that is checkable coordinate by
coordinate.

**Construction.**  Start from the top-left vertex `V 1 = (b₀ ^ K, b₀)`.  For each interior ray
`ρ j` walk along the edge direction `(ρ j).2, -(ρ j).1` (so `a` increases and `b` decreases)
until the log-state is exactly `2δ‖ρ j‖₁` past the line of `ρ j` (`exists_edge_step`, an
intermediate-value argument); that point is `V j`.  The polygon has a vertical edge through
`V 1`, the interior edges `[V (j-1), V j]` with normals `ρ j`, and a horizontal edge through
`V (k+1)`.

**What is proved.**

* `cross_logState_edgePt_mono`: along an edge, the signed position `cross σ (U z)` of the
  log-state relative to *every* ray `σ` of the quadrant is nondecreasing — the planar form of
  Craciun's Lemma 9.10.
* `cross_next_le_of_depth`: once the log-state is `2δ‖ρ j‖₁` past `ρ j` and deep enough, it is
  `2δ‖ρ (j+1)‖₁` before `ρ (j+1)`.
* `exists_polygon`: for every small `b₀` there are offsets `c j > 0` such that the region
  `{z | ∀ j, c j ≤ ⟪ρ j, z⟫}` contains the quadrant above `(b₀ ^ K, b₀)`, and at every point of
  the region where the constraint `j` is active (inside the box `(0, e^{-2δ}]²`) the log-state is
  `Good`: at least `2δ‖·‖₁` past `ρ (j-1)` and before `ρ (j+1)`.  For a planar fan these are
  exactly the points whose every fan cone within `δ` contains `ρ j`, which is the descent
  condition of a toric differential inclusion.

Nothing here is an axiom or a `sorry`.
-/

open Real

namespace CRNT
namespace PlanarZSH

/-- The planar cross product `u × v`. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The planar dot product. -/
def pair (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The ℓ¹ size of a vector of the quadrant. -/
def nrm (u : ℝ × ℝ) : ℝ := u.1 + u.2

/-- The log-state `(-log a, -log b)`. -/
noncomputable def logState (z : ℝ × ℝ) : ℝ × ℝ := (-Real.log z.1, -Real.log z.2)

/-- The point at parameter `s` on the edge through `W` with normal `ρ`. -/
def edgePt (W ρ : ℝ × ℝ) (s : ℝ) : ℝ × ℝ := (W.1 + s * ρ.2, W.2 - s * ρ.1)

/-- The log-state is `2δ`-past `ρm` and `2δ`-before `ρp`. -/
def Good (δ : ℝ) (ρm ρp U : ℝ × ℝ) : Prop :=
  2 * δ * nrm ρm ≤ cross ρm U ∧ cross ρp U ≤ -(2 * δ * nrm ρp)

theorem cross_logState (σ z : ℝ × ℝ) :
    cross σ (logState z) = -σ.1 * Real.log z.2 + σ.2 * Real.log z.1 := by
  simp only [cross, logState]; ring

theorem pair_edgePt (σ W ρ : ℝ × ℝ) (s : ℝ) :
    pair σ (edgePt W ρ s) = pair σ W + s * cross σ ρ := by
  simp [pair, edgePt, cross]; ring

theorem pair_self_edgePt (W ρ : ℝ × ℝ) (s : ℝ) : pair ρ (edgePt W ρ s) = pair ρ W := by
  rw [pair_edgePt]; simp only [cross]; ring

/-- **Monotonicity along an edge.** -/
theorem cross_logState_edgePt_mono {W ρ σ : ℝ × ℝ} (hW1 : 0 < W.1) (hρ1 : 0 ≤ ρ.1)
    (hρ2 : 0 ≤ ρ.2) (hσ1 : 0 ≤ σ.1) (hσ2 : 0 ≤ σ.2) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s')
    (hpos : 0 < (edgePt W ρ s').2) :
    cross σ (logState (edgePt W ρ s)) ≤ cross σ (logState (edgePt W ρ s')) := by
  rw [cross_logState, cross_logState]
  simp only [edgePt] at hpos ⊢
  have ha : 0 < W.1 + s * ρ.2 := by nlinarith
  have hb' : 0 < W.2 - s' * ρ.1 := hpos
  have hb : 0 < W.2 - s * ρ.1 := by nlinarith
  have h1 : Real.log (W.1 + s * ρ.2) ≤ Real.log (W.1 + s' * ρ.2) :=
    Real.log_le_log ha (by nlinarith)
  have h2 : Real.log (W.2 - s' * ρ.1) ≤ Real.log (W.2 - s * ρ.1) :=
    Real.log_le_log hb' (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hσ2, mul_le_mul_of_nonneg_left h2 hσ1]

/-- **One step of the construction (intermediate value).** -/
theorem exists_edge_step {W ρ : ℝ × ℝ} (hW1 : 0 < W.1) (hW2 : 0 < W.2) (hρ1 : 0 < ρ.1)
    (hρ2 : 0 < ρ.2) {θ : ℝ} (hθ : cross ρ (logState W) < θ) :
    ∃ s, 0 < s ∧ s < W.2 / ρ.1 ∧ cross ρ (logState (edgePt W ρ s)) = θ := by
  set β : ℝ := min (W.2 / 2) (Real.exp ((ρ.2 * Real.log W.1 - θ) / ρ.1 - 1)) with hβ
  have hβpos : 0 < β := lt_min (half_pos hW2) (Real.exp_pos _)
  have hβlt : β < W.2 := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hW2)
  set s' : ℝ := (W.2 - β) / ρ.1 with hs'
  have hs'pos : 0 < s' := div_pos (by linarith) hρ1
  have hb' : (edgePt W ρ s').2 = β := by
    simp only [edgePt, hs']; field_simp; ring
  have hs'lt : s' < W.2 / ρ.1 := by
    rw [hs']; exact div_lt_div_of_pos_right (by linarith) hρ1
  set f : ℝ → ℝ := fun s => cross ρ (logState (edgePt W ρ s)) with hf
  have hcont : ContinuousOn f (Set.Icc 0 s') := by
    have : ∀ s ∈ Set.Icc 0 s', f s =
        -ρ.1 * Real.log (W.2 - s * ρ.1) + ρ.2 * Real.log (W.1 + s * ρ.2) := by
      intro s _; simp only [hf, cross_logState, edgePt]
    refine ContinuousOn.congr ?_ this
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (by fun_prop)
      intro s hs
      have : W.2 - s * ρ.1 ≥ W.2 - s' * ρ.1 := by nlinarith [hs.2]
      have h2 : W.2 - s' * ρ.1 = β := by simpa [edgePt] using hb'
      linarith
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (by fun_prop)
      intro s hs; nlinarith [hs.1]
  have hf0 : f 0 = cross ρ (logState W) := by simp [hf, edgePt]
  have hfs' : θ < f s' := by
    simp only [hf, cross_logState]
    rw [hb']
    have hlogβ : Real.log β ≤ (ρ.2 * Real.log W.1 - θ) / ρ.1 - 1 := by
      calc Real.log β ≤ Real.log (Real.exp ((ρ.2 * Real.log W.1 - θ) / ρ.1 - 1)) :=
            Real.log_le_log hβpos (min_le_right _ _)
        _ = _ := Real.log_exp _
    have ha : Real.log W.1 ≤ Real.log (edgePt W ρ s').1 := by
      apply Real.log_le_log hW1; simp only [edgePt]; nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlogβ hρ1.le
    have hexp : ρ.1 * ((ρ.2 * Real.log W.1 - θ) / ρ.1 - 1) =
        ρ.2 * Real.log W.1 - θ - ρ.1 := by field_simp
    rw [hexp] at hmul
    nlinarith [mul_le_mul_of_nonneg_left ha hρ2.le]
  obtain ⟨s, hsI, hsv⟩ := intermediate_value_Icc hs'pos.le hcont ⟨by rw [hf0]; exact hθ.le, hfs'.le⟩
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [hf0] at hsv; exact absurd hsv (ne_of_lt hθ)
  exact ⟨s, lt_of_le_of_ne hsI.1 (Ne.symm hs0), lt_of_le_of_lt hsI.2 hs'lt, hsv⟩

/-- **Depth lemma.**  Exactly `2δ‖ρ‖₁` past `ρ` and deep enough ⇒ `2δ‖σ‖₁` before `σ`, for the
next ray `σ` counterclockwise. -/
theorem cross_next_le_of_depth {ρ σ U : ℝ × ℝ} {δ : ℝ} (hρn : 0 < nrm ρ)
    (hg : 0 < cross ρ σ) (hU : cross ρ U = 2 * δ * nrm ρ)
    (hdepth : 4 * δ * nrm ρ * nrm σ / cross ρ σ ≤ U.1 + U.2) :
    cross σ U ≤ -(2 * δ * nrm σ) := by
  -- `cross ρ σ · (U₁ + U₂) = cross U σ · ‖ρ‖₁ + cross ρ U · ‖σ‖₁`
  have hid : cross ρ σ * (U.1 + U.2) = (-cross σ U) * nrm ρ + cross ρ U * nrm σ := by
    simp [cross, nrm]; ring
  have hd : 4 * δ * nrm ρ * nrm σ ≤ cross ρ σ * (U.1 + U.2) := by
    rw [div_le_iff₀ hg] at hdepth; linarith
  rw [hid, hU] at hd
  have : 2 * δ * nrm ρ * nrm σ ≤ (-cross σ U) * nrm ρ := by nlinarith
  have h2 : 2 * δ * nrm σ ≤ -cross σ U := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hρn
    nlinarith
  linarith

/-! ## Logarithmic bounds and their stability -/

theorem cross_ge_of_bounds {σ z : ℝ × ℝ} (hσ1 : 0 ≤ σ.1) (hσ2 : 0 ≤ σ.2) {lo1 hi2 : ℝ}
    (hlo1 : 0 < lo1) (h1 : lo1 ≤ z.1) (hz2 : 0 < z.2) (h2 : z.2 ≤ hi2) :
    -σ.1 * Real.log hi2 + σ.2 * Real.log lo1 ≤ cross σ (logState z) := by
  rw [cross_logState]
  have a := Real.log_le_log hlo1 h1
  have b := Real.log_le_log hz2 h2
  nlinarith [mul_le_mul_of_nonneg_left a hσ2, mul_le_mul_of_nonneg_left b hσ1]

theorem cross_le_of_bounds {σ z : ℝ × ℝ} (hσ1 : 0 ≤ σ.1) (hσ2 : 0 ≤ σ.2) {hi1 lo2 : ℝ}
    (hz1 : 0 < z.1) (h1 : z.1 ≤ hi1) (hlo2 : 0 < lo2) (h2 : lo2 ≤ z.2) :
    cross σ (logState z) ≤ -σ.1 * Real.log lo2 + σ.2 * Real.log hi1 := by
  rw [cross_logState]
  have a := Real.log_le_log hz1 h1
  have b := Real.log_le_log hlo2 h2
  nlinarith [mul_le_mul_of_nonneg_left a hσ2, mul_le_mul_of_nonneg_left b hσ1]

theorem continuousAt_logpair (σ1 σ2 x0 x1 y0 y1 : ℝ) (hx : 0 < x0) (hy : 0 < y0) :
    ContinuousAt (fun e : ℝ => -σ1 * Real.log (x0 + e * x1) + σ2 * Real.log (y0 + e * y1)) 0 := by
  apply ContinuousAt.add
  · apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.log (by fun_prop); simp; exact hx.ne'
  · apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.log (by fun_prop); simp; exact hy.ne'

theorem eventually_pos_affine {x0 x1 : ℝ} (hx : 0 < x0) :
    ∀ᶠ e in nhds (0 : ℝ), 0 < x0 + e * x1 := by
  have : ContinuousAt (fun e : ℝ => x0 + e * x1) 0 := by fun_prop
  have h := this.tendsto
  simp only [zero_mul, add_zero] at h
  exact h.eventually_const_lt hx

theorem eventually_logpair_gt {σ1 σ2 x0 x1 y0 y1 T : ℝ} (hx : 0 < x0) (hy : 0 < y0)
    (h : T < -σ1 * Real.log x0 + σ2 * Real.log y0) :
    ∀ᶠ e in nhds (0 : ℝ), T < -σ1 * Real.log (x0 + e * x1) + σ2 * Real.log (y0 + e * y1) := by
  have hc := (continuousAt_logpair σ1 σ2 x0 x1 y0 y1 hx hy).tendsto
  simp only [zero_mul, add_zero] at hc
  exact hc.eventually_const_lt h

theorem eventually_logpair_lt {σ1 σ2 x0 x1 y0 y1 T : ℝ} (hx : 0 < x0) (hy : 0 < y0)
    (h : -σ1 * Real.log x0 + σ2 * Real.log y0 < T) :
    ∀ᶠ e in nhds (0 : ℝ), -σ1 * Real.log (x0 + e * x1) + σ2 * Real.log (y0 + e * y1) < T := by
  have hc := (continuousAt_logpair σ1 σ2 x0 x1 y0 y1 hx hy).tendsto
  simp only [zero_mul, add_zero] at hc
  exact hc.eventually_lt_const h

/-! ## The ray data and the vertex chain -/

/-- A planar fan of the closed quadrant: `ρ 0 = ρ 1 = e₁`, `ρ (k+2) = ρ (k+3) = e₂`, interior rays
in the open quadrant, strictly ordered counterclockwise. -/
structure Rays where
  k : ℕ
  ρ : ℕ → ℝ × ℝ
  ρ0 : ρ 0 = (1, 0)
  ρ1 : ρ 1 = (1, 0)
  ρk2 : ρ (k + 2) = (0, 1)
  ρk3 : ρ (k + 3) = (0, 1)
  interior : ∀ j, 2 ≤ j → j ≤ k + 1 → 0 < (ρ j).1 ∧ 0 < (ρ j).2
  order : ∀ i j, 1 ≤ i → i < j → j ≤ k + 2 → 0 < cross (ρ i) (ρ j)

namespace Rays

variable (F : Rays)

theorem nonneg (j : ℕ) (hj : j ≤ F.k + 3) : 0 ≤ (F.ρ j).1 ∧ 0 ≤ (F.ρ j).2 := by
  rcases Nat.lt_or_ge j 2 with h | h
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [F.ρ0, F.ρ1]
  · rcases Nat.lt_or_ge (F.k + 1) j with h' | h'
    · have : j = F.k + 2 ∨ j = F.k + 3 := by omega
      rcases this with rfl | rfl <;> simp [F.ρk2, F.ρk3]
    · exact ⟨(F.interior j h h').1.le, (F.interior j h h').2.le⟩

theorem nrm_pos (j : ℕ) (hj : j ≤ F.k + 3) : 0 < nrm (F.ρ j) := by
  rcases Nat.lt_or_ge j 2 with h | h
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [nrm, F.ρ0, F.ρ1]
  · rcases Nat.lt_or_ge (F.k + 1) j with h' | h'
    · have : j = F.k + 2 ∨ j = F.k + 3 := by omega
      rcases this with rfl | rfl <;> simp [nrm, F.ρk2, F.ρk3]
    · have := F.interior j h h'; simp only [nrm]; linarith

/-- The ratio budget `Q = ∑ (ρ j).2 / (ρ j).1` over the interior rays. -/
noncomputable def Q : ℝ := ∑ j ∈ Finset.Icc 2 (F.k + 1), (F.ρ j).2 / (F.ρ j).1

theorem Q_nonneg : 0 ≤ F.Q :=
  Finset.sum_nonneg fun j hj => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    exact (div_pos (F.interior j h1 h2).2 (F.interior j h1 h2).1).le

theorem ratio_le_Q (j : ℕ) (h1 : 2 ≤ j) (h2 : j ≤ F.k + 1) : (F.ρ j).2 / (F.ρ j).1 ≤ F.Q :=
  Finset.single_le_sum (f := fun j => (F.ρ j).2 / (F.ρ j).1)
    (fun i hi => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
      exact (div_pos (F.interior i h1 h2).2 (F.interior i h1 h2).1).le)
    (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- The depth budget `D ≥ 4δ‖ρ j‖₁‖ρ (j+1)‖₁ / (ρ j × ρ (j+1))` for every consecutive pair. -/
noncomputable def D (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (F.k + 1),
    |4 * δ * nrm (F.ρ j) * nrm (F.ρ (j + 1)) / cross (F.ρ j) (F.ρ (j + 1))|

theorem depth_le_D (δ : ℝ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ F.k + 1) :
    4 * δ * nrm (F.ρ j) * nrm (F.ρ (j + 1)) / cross (F.ρ j) (F.ρ (j + 1)) ≤ F.D δ :=
  (le_abs_self _).trans (Finset.single_le_sum
    (f := fun j => |4 * δ * nrm (F.ρ j) * nrm (F.ρ (j + 1)) / cross (F.ρ j) (F.ρ (j + 1))|)
    (fun _ _ => abs_nonneg _) (Finset.mem_Icc.mpr ⟨h1, h2⟩))

end Rays

open Classical in
/-- The edge parameter chosen by `exists_edge_step` (zero when its hypotheses fail). -/
noncomputable def stepS (W ρ : ℝ × ℝ) (θ : ℝ) : ℝ :=
  if h : 0 < W.1 ∧ 0 < W.2 ∧ 0 < ρ.1 ∧ 0 < ρ.2 ∧ cross ρ (logState W) < θ then
    Classical.choose (exists_edge_step h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else 0

theorem stepS_spec {W ρ : ℝ × ℝ} {θ : ℝ} (hW1 : 0 < W.1) (hW2 : 0 < W.2) (hρ1 : 0 < ρ.1)
    (hρ2 : 0 < ρ.2) (hθ : cross ρ (logState W) < θ) :
    0 < stepS W ρ θ ∧ stepS W ρ θ < W.2 / ρ.1 ∧
      cross ρ (logState (edgePt W ρ (stepS W ρ θ))) = θ := by
  have h : 0 < W.1 ∧ 0 < W.2 ∧ 0 < ρ.1 ∧ 0 < ρ.2 ∧ cross ρ (logState W) < θ :=
    ⟨hW1, hW2, hρ1, hρ2, hθ⟩
  unfold stepS
  rw [dif_pos h]
  exact Classical.choose_spec (exists_edge_step h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

namespace Rays

variable (F : Rays)

/-- The vertex chain from the top-left vertex `V₁`. -/
noncomputable def vert (δ : ℝ) (V₁ : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => V₁
  | 1 => V₁
  | (j + 2) => edgePt (vert δ V₁ (j + 1)) (F.ρ (j + 2))
      (stepS (vert δ V₁ (j + 1)) (F.ρ (j + 2)) (2 * δ * nrm (F.ρ (j + 2))))

/-- The edge parameters of the chain. -/
noncomputable def par (δ : ℝ) (V₁ : ℝ × ℝ) (j : ℕ) : ℝ :=
  stepS (F.vert δ V₁ (j - 1)) (F.ρ j) (2 * δ * nrm (F.ρ j))

theorem vert_succ (δ : ℝ) (V₁ : ℝ × ℝ) (j : ℕ) (hj : 1 ≤ j) :
    F.vert δ V₁ (j + 1) = edgePt (F.vert δ V₁ j) (F.ρ (j + 1)) (F.par δ V₁ (j + 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp [vert, par]

/-- **The chain invariant.** -/
theorem chain (δ : ℝ) (hδ : 0 < δ) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hdepth : F.D δ ≤ -Real.log b₀) (hsmall : a₀ + b₀ * (F.k * F.Q) ≤ 1)
    (hV1 : cross (F.ρ 2) (logState (a₀, b₀)) ≤ -(2 * δ * nrm (F.ρ 2))) :
    ∀ j, 1 ≤ j → j ≤ F.k + 1 →
      0 < (F.vert δ (a₀, b₀) j).1 ∧ 0 < (F.vert δ (a₀, b₀) j).2 ∧
      (F.vert δ (a₀, b₀) j).2 ≤ b₀ ∧ (F.vert δ (a₀, b₀) j).1 ≤ a₀ + b₀ * ((j - 1 : ℕ) * F.Q) ∧
      (2 ≤ j → cross (F.ρ j) (logState (F.vert δ (a₀, b₀) j)) = 2 * δ * nrm (F.ρ j)) ∧
      (2 ≤ j → 0 < F.par δ (a₀, b₀) j ∧
        F.par δ (a₀, b₀) j < (F.vert δ (a₀, b₀) (j - 1)).2 / (F.ρ j).1) ∧
      cross (F.ρ (j + 1)) (logState (F.vert δ (a₀, b₀) j)) ≤ -(2 * δ * nrm (F.ρ (j + 1))) := by
  intro j hj1 hjk
  induction j, hj1 using Nat.le_induction with
  | base =>
    have hv1 : F.vert δ (a₀, b₀) 1 = (a₀, b₀) := rfl
    rw [hv1]
    exact ⟨ha₀, hb₀, le_refl _, by simp, fun h => absurd h (by norm_num),
      fun h => absurd h (by norm_num), hV1⟩
  | succ j hj ih =>
    obtain ⟨hp1, hp2, hb, ha, -, -, hnext⟩ := ih (by omega)
    have hint := F.interior (j + 1) (by omega) hjk
    have hθ : cross (F.ρ (j + 1)) (logState (F.vert δ (a₀, b₀) j)) <
        2 * δ * nrm (F.ρ (j + 1)) := by
      have := F.nrm_pos (j + 1) (by omega)
      have : 0 < 2 * δ * nrm (F.ρ (j + 1)) := by positivity
      linarith
    obtain ⟨hs0, hslt, hscross⟩ := stepS_spec hp1 hp2 hint.1 hint.2 hθ
    have hpar : F.par δ (a₀, b₀) (j + 1) =
        stepS (F.vert δ (a₀, b₀) j) (F.ρ (j + 1)) (2 * δ * nrm (F.ρ (j + 1))) := by
      simp [par]
    have hv : F.vert δ (a₀, b₀) (j + 1) = edgePt (F.vert δ (a₀, b₀) j) (F.ρ (j + 1))
        (F.par δ (a₀, b₀) (j + 1)) := F.vert_succ δ (a₀, b₀) j hj
    rw [← hpar] at hs0 hslt hscross
    rw [hv]
    set W := F.vert δ (a₀, b₀) j with hW
    set s := F.par δ (a₀, b₀) (j + 1) with hsdef
    have hsρ : s * (F.ρ (j + 1)).1 < W.2 := by
      rwa [lt_div_iff₀ hint.1] at hslt
    have hnew1 : 0 < (edgePt W (F.ρ (j + 1)) s).1 := by
      simp only [edgePt]; nlinarith [hint.2]
    have hnew2 : 0 < (edgePt W (F.ρ (j + 1)) s).2 := by simp only [edgePt]; linarith
    have hnewb : (edgePt W (F.ρ (j + 1)) s).2 ≤ b₀ := by
      simp only [edgePt]; nlinarith [hint.1]
    have hratio := F.ratio_le_Q (j + 1) (by omega) hjk
    have hnewa : (edgePt W (F.ρ (j + 1)) s).1 ≤ a₀ + b₀ * ((j + 1 - 1 : ℕ) * F.Q) := by
      simp only [edgePt]
      have h1 : s * (F.ρ (j + 1)).2 ≤ b₀ * ((F.ρ (j + 1)).2 / (F.ρ (j + 1)).1) := by
        have : s ≤ W.2 / (F.ρ (j + 1)).1 := hslt.le
        have h2 : s * (F.ρ (j + 1)).2 ≤ W.2 / (F.ρ (j + 1)).1 * (F.ρ (j + 1)).2 :=
          mul_le_mul_of_nonneg_right this hint.2.le
        have h3 : W.2 / (F.ρ (j + 1)).1 * (F.ρ (j + 1)).2 =
            W.2 * ((F.ρ (j + 1)).2 / (F.ρ (j + 1)).1) := by ring
        have h4 : W.2 * ((F.ρ (j + 1)).2 / (F.ρ (j + 1)).1) ≤
            b₀ * ((F.ρ (j + 1)).2 / (F.ρ (j + 1)).1) :=
          mul_le_mul_of_nonneg_right hb (div_pos hint.2 hint.1).le
        linarith
      have h5 : b₀ * ((F.ρ (j + 1)).2 / (F.ρ (j + 1)).1) ≤ b₀ * F.Q :=
        mul_le_mul_of_nonneg_left hratio hb₀.le
      have hjj : ((j + 1 - 1 : ℕ) : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
        rw [show j + 1 - 1 = (j - 1) + 1 by omega]; push_cast; ring
      rw [hjj]
      nlinarith
    refine ⟨hnew1, hnew2, hnewb, hnewa, fun _ => hscross, fun _ => ⟨hs0, by simpa using hslt⟩, ?_⟩
    -- the next ray, by the depth lemma
    by_cases hlast : j + 1 = F.k + 1
    · -- next ray is `e₂`
      have hk2 : F.ρ (j + 1 + 1) = (0, 1) := by rw [show j + 1 + 1 = F.k + 2 by omega]; exact F.ρk2
      rw [hk2]
      simp only [cross, nrm, logState]
      have ha1 : (edgePt W (F.ρ (j + 1)) s).1 ≤ 1 := by
        have : ((j + 1 - 1 : ℕ) : ℝ) ≤ F.k := by exact_mod_cast (by omega : j + 1 - 1 ≤ F.k)
        have := mul_le_mul_of_nonneg_right this F.Q_nonneg
        nlinarith [hnewa]
      -- use the depth lemma with `σ = e₂`
      have hg := F.order (j + 1) (F.k + 2) (by omega) (by omega) le_rfl
      rw [F.ρk2] at hg
      have hdl := cross_next_le_of_depth (ρ := F.ρ (j + 1)) (σ := (0, 1))
        (U := logState (edgePt W (F.ρ (j + 1)) s)) (δ := δ) (F.nrm_pos (j + 1) (by omega)) hg
        hscross ?_
      · simpa [cross, nrm, logState] using hdl
      · have hU1 : 0 ≤ (logState (edgePt W (F.ρ (j + 1)) s)).1 := by
          simp only [logState]; exact neg_nonneg.mpr (Real.log_nonpos hnew1.le ha1)
        have hU2 : -Real.log b₀ ≤ (logState (edgePt W (F.ρ (j + 1)) s)).2 := by
          simp only [logState]; exact neg_le_neg (Real.log_le_log hnew2 hnewb)
        have := F.depth_le_D δ (j + 1) (by omega) hjk
        rw [show j + 1 + 1 = F.k + 2 by omega, F.ρk2] at this
        linarith
    · have hg := F.order (j + 1) (j + 1 + 1) (by omega) (by omega) (by omega)
      refine cross_next_le_of_depth (F.nrm_pos (j + 1) (by omega)) hg hscross ?_
      have ha1 : (edgePt W (F.ρ (j + 1)) s).1 ≤ 1 := by
        have : ((j + 1 - 1 : ℕ) : ℝ) ≤ F.k := by exact_mod_cast (by omega : j + 1 - 1 ≤ F.k)
        have := mul_le_mul_of_nonneg_right this F.Q_nonneg
        nlinarith [hnewa]
      have hU1 : 0 ≤ (logState (edgePt W (F.ρ (j + 1)) s)).1 := by
        simp only [logState]; exact neg_nonneg.mpr (Real.log_nonpos hnew1.le ha1)
      have hU2 : -Real.log b₀ ≤ (logState (edgePt W (F.ρ (j + 1)) s)).2 := by
        simp only [logState]; exact neg_le_neg (Real.log_le_log hnew2 hnewb)
      have := F.depth_le_D δ (j + 1) (by omega) hjk
      linarith

/-! ## The polygon -/

/-- The offsets `c j = ⟪ρ j, V j⟫` (with `V (k+1)` used for the last, horizontal edge). -/
noncomputable def off (δ : ℝ) (V₁ : ℝ × ℝ) (j : ℕ) : ℝ :=
  pair (F.ρ j) (F.vert δ V₁ (min j (F.k + 1)))

/-- Membership in the region above the polygon. -/
def InR (c : ℕ → ℝ) (z : ℝ × ℝ) : Prop := ∀ i, 1 ≤ i → i ≤ F.k + 2 → c i ≤ pair (F.ρ i) z

/-- The band property at width `e`: points of the shifted region `R_e = {c i + e ≤ ⟪ρ i, z⟫}`
on the active edge `j` are `Good (δ / 2)` — the edge margin survives at half strength. -/
def BandGood (δ : ℝ) (c : ℕ → ℝ) (e : ℝ) (j : ℕ) : Prop :=
  ∀ z : ℝ × ℝ, 0 < z.1 → 0 < z.2 → z.1 ≤ Real.exp (-(2 * δ)) → z.2 ≤ Real.exp (-(2 * δ)) →
    (∀ i, 1 ≤ i → i ≤ F.k + 2 → c i + e ≤ pair (F.ρ i) z) → pair (F.ρ j) z = c j + e →
    Good (δ / 2) (F.ρ (j - 1)) (F.ρ (j + 1)) (logState z)

section Polygon

variable {δ : ℝ} (hδ : 0 < δ) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
  (hdepth : F.D δ ≤ -Real.log b₀) (hsmall : a₀ + b₀ * (F.k * F.Q) ≤ 1)
  (hV1 : cross (F.ρ 2) (logState (a₀, b₀)) ≤ -(2 * δ * nrm (F.ρ 2)))
  (hb2δ : b₀ ≤ Real.exp (-(2 * δ)))

include hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ

theorem past_vert (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ F.k + 1) :
    2 * δ * nrm (F.ρ i) ≤ cross (F.ρ i) (logState (F.vert δ (a₀, b₀) i)) := by
  rcases Nat.lt_or_ge i 2 with h | h
  · have hi : i = 1 := by omega
    subst hi
    have hv1 : F.vert δ (a₀, b₀) 1 = (a₀, b₀) := rfl
    rw [hv1, F.ρ1]
    simp only [cross, nrm, logState]
    have : Real.log b₀ ≤ -(2 * δ) := by
      calc Real.log b₀ ≤ Real.log (Real.exp (-(2 * δ))) := Real.log_le_log hb₀ hb2δ
        _ = _ := Real.log_exp _
    linarith
  · exact ((F.chain δ hδ ha₀ hb₀ hdepth hsmall hV1 i hi1 hik).2.2.2.2.1 h).ge

theorem pair_vert_le (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ F.k + 2) :
    ∀ m, 1 ≤ m → m ≤ min j (F.k + 1) →
      pair (F.ρ j) (F.vert δ (a₀, b₀) m) ≤ pair (F.ρ j) (a₀, b₀) := by
  intro m hm1 hmj
  induction m, hm1 using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    have hprev := ih (by omega)
    have hch := F.chain δ hδ ha₀ hb₀ hdepth hsmall hV1 (m + 1) (by omega) (by omega)
    obtain ⟨hs0, -⟩ := hch.2.2.2.2.2.1 (by omega)
    rw [F.vert_succ δ (a₀, b₀) m hm, pair_edgePt]
    have hcr : cross (F.ρ j) (F.ρ (m + 1)) ≤ 0 := by
      rcases Nat.lt_or_ge (m + 1) j with hlt | hge
      · have := F.order (m + 1) j (by omega) hlt hjk
        simp only [cross] at this ⊢; linarith
      · have : m + 1 = j := by omega
        subst this; simp [cross]; ring_nf; exact le_refl _
    nlinarith

/-- **The polygon.** -/
theorem polygon :
    (∀ j, 1 ≤ j → j ≤ F.k + 2 → 0 < F.off δ (a₀, b₀) j) ∧
    (∀ z : ℝ × ℝ, a₀ ≤ z.1 → b₀ ≤ z.2 → F.InR (F.off δ (a₀, b₀)) z) ∧
    (∀ z : ℝ × ℝ, 0 < z.1 → 0 < z.2 → z.1 ≤ Real.exp (-(2 * δ)) → z.2 ≤ Real.exp (-(2 * δ)) →
      F.InR (F.off δ (a₀, b₀)) z → ∀ j, 1 ≤ j → j ≤ F.k + 2 →
        pair (F.ρ j) z = F.off δ (a₀, b₀) j →
        Good δ (F.ρ (j - 1)) (F.ρ (j + 1)) (logState z)) := by
  have hch := F.chain δ hδ ha₀ hb₀ hdepth hsmall hV1
  have hlog2δ : ∀ x, 0 < x → x ≤ Real.exp (-(2 * δ)) → Real.log x ≤ -(2 * δ) := fun x hx h => by
    calc Real.log x ≤ Real.log (Real.exp (-(2 * δ))) := Real.log_le_log hx h
      _ = _ := Real.log_exp _
  refine ⟨?_, ?_, ?_⟩
  · -- positivity of the offsets
    intro j hj1 hjk
    obtain ⟨hp1, hp2, -⟩ := hch (min j (F.k + 1)) (by omega) (by omega)
    obtain ⟨hn1, hn2⟩ := F.nonneg j (by omega)
    have hn := F.nrm_pos j (by omega)
    simp only [off, pair, nrm] at hn ⊢
    rcases (lt_or_eq_of_le hn1) with h1 | h1
    · nlinarith
    · have : 0 < (F.ρ j).2 := by linarith
      nlinarith
  · -- the quadrant above `V₁`
    intro z hz1 hz2 i hi1 hik
    obtain ⟨hn1, hn2⟩ := F.nonneg i (by omega)
    have h1 := F.pair_vert_le hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ i hi1 hik (min i (F.k + 1))
      (by omega) le_rfl
    have h2 : pair (F.ρ i) (a₀, b₀) ≤ pair (F.ρ i) z := by
      simp only [pair]; nlinarith
    exact h1.trans h2
  · intro z hz1 hz2 hzb1 hzb2 hR j hj1 hjk hact
    rcases Nat.lt_or_ge j 2 with hj | hj
    · -- the vertical edge
      have hj1' : j = 1 := by omega
      subst hj1'
      have hc1 : F.off δ (a₀, b₀) 1 = a₀ := by
        simp [off, F.ρ1, pair, show min 1 (F.k + 1) = 1 by omega, vert]
      have hza : z.1 = a₀ := by
        rw [hc1] at hact; simpa [pair, F.ρ1] using hact
      have hρ22 : 0 < (F.ρ 2).2 := by
        have := F.order 1 2 le_rfl (by norm_num) (by omega)
        simpa [cross, F.ρ1] using this
      have hc2 : F.off δ (a₀, b₀) 2 = pair (F.ρ 2) (a₀, b₀) := by
        unfold off
        rcases Nat.lt_or_ge (F.k + 1) 2 with hk | hk
        · rw [show min 2 (F.k + 1) = 1 by omega]; rfl
        · rw [show min 2 (F.k + 1) = 2 by omega,
            show (2 : ℕ) = 1 + 1 from rfl, F.vert_succ δ (a₀, b₀) 1 le_rfl, pair_self_edgePt]
          rfl
      have hR2 := hR 2 (by norm_num) (by omega)
      rw [hc2] at hR2
      have hzb : b₀ ≤ z.2 := by
        simp only [pair] at hR2; rw [hza] at hR2; nlinarith
      refine ⟨?_, ?_⟩
      · rw [show (1 - 1 : ℕ) = 0 from rfl, F.ρ0]
        simp only [cross, nrm, logState]
        have := hlog2δ z.2 hz2 hzb2; linarith
      · rw [cross_logState]
        have hle : cross (F.ρ 2) (logState (a₀, b₀)) =
            -(F.ρ 2).1 * Real.log b₀ + (F.ρ 2).2 * Real.log a₀ := cross_logState _ _
        have hlogb : Real.log b₀ ≤ Real.log z.2 := Real.log_le_log hb₀ hzb
        have hn := (F.nonneg 2 (by omega)).1
        rw [hza]
        nlinarith [mul_le_mul_of_nonneg_left hlogb hn]
    · rcases Nat.lt_or_ge (F.k + 1) j with hjl | hjl
      · -- the horizontal edge
        have hjk2 : j = F.k + 2 := by omega
        subst hjk2
        set V := F.vert δ (a₀, b₀) (F.k + 1) with hV
        have hcl : F.off δ (a₀, b₀) (F.k + 2) = V.2 := by
          simp [off, F.ρk2, pair, show min (F.k + 2) (F.k + 1) = F.k + 1 by omega, hV]
        have hzb : z.2 = V.2 := by rw [hcl] at hact; simpa [pair, F.ρk2] using hact
        have hρ1 : 0 < (F.ρ (F.k + 1)).1 := by
          have := F.order (F.k + 1) (F.k + 2) (by omega) (by omega) le_rfl
          simpa [cross, F.ρk2] using this
        have hck : F.off δ (a₀, b₀) (F.k + 1) = pair (F.ρ (F.k + 1)) V := by
          simp [off, hV]
        have hRk := hR (F.k + 1) (by omega) (by omega)
        rw [hck] at hRk
        obtain ⟨hV1p, hV2p, -⟩ := hch (F.k + 1) (by omega) le_rfl
        have hza : V.1 ≤ z.1 := by
          simp only [pair] at hRk; rw [hzb] at hRk; nlinarith
        refine ⟨?_, ?_⟩
        · rw [show F.k + 2 - 1 = F.k + 1 by omega]
          have hp := F.past_vert hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ (F.k + 1) (by omega) le_rfl
          rw [← hV, cross_logState] at hp
          rw [cross_logState, hzb]
          have hloga : Real.log V.1 ≤ Real.log z.1 := Real.log_le_log hV1p hza
          have hn := (F.nonneg (F.k + 1) (by omega)).2
          nlinarith [mul_le_mul_of_nonneg_left hloga hn]
        · rw [show F.k + 2 + 1 = F.k + 3 by omega, F.ρk3]
          simp only [cross, nrm, logState]
          have := hlog2δ z.1 hz1 hzb1; linarith
      · -- an interior edge
        set W := F.vert δ (a₀, b₀) (j - 1) with hW
        set sj := F.par δ (a₀, b₀) j with hsj
        have hint := F.interior j hj hjl
        have hvj : F.vert δ (a₀, b₀) j = edgePt W (F.ρ j) sj := by
          have := F.vert_succ δ (a₀, b₀) (j - 1) (by omega)
          rwa [show j - 1 + 1 = j by omega] at this
        obtain ⟨hW1, hW2, -⟩ := hch (j - 1) (by omega) (by omega)
        obtain ⟨hVj1, hVj2, -, -, -, hpar, hnext⟩ := hch j (by omega) hjl
        obtain ⟨hs0, hslt⟩ := hpar hj
        have hcj : F.off δ (a₀, b₀) j = pair (F.ρ j) W := by
          simp only [off, show min j (F.k + 1) = j by omega]; rw [hvj, pair_self_edgePt]
        rw [hcj] at hact
        -- `z` lies on the line through `W`
        set t := (z.1 - W.1) / (F.ρ j).2 with ht
        have hρ2ne : (F.ρ j).2 ≠ 0 := hint.2.ne'
        have e1' : t * (F.ρ j).2 = z.1 - W.1 := by rw [ht]; field_simp
        have key : (F.ρ j).2 * (z.2 - W.2 + t * (F.ρ j).1) = 0 := by
          have hexp : (F.ρ j).2 * (z.2 - W.2 + t * (F.ρ j).1) =
              (F.ρ j).2 * z.2 - (F.ρ j).2 * W.2 + (F.ρ j).1 * (t * (F.ρ j).2) := by ring
          rw [hexp, e1']; simp only [pair] at hact; linarith
        have e2 := (mul_eq_zero.mp key).resolve_left hρ2ne
        have hzt : z = edgePt W (F.ρ j) t :=
          Prod.ext (by simp only [edgePt]; linarith) (by simp only [edgePt]; linarith)
        -- the previous constraint gives `0 ≤ t`
        have hcprev : F.off δ (a₀, b₀) (j - 1) = pair (F.ρ (j - 1)) W := by
          simp only [off, show min (j - 1) (F.k + 1) = j - 1 by omega, hW]
        have hRp := hR (j - 1) (by omega) (by omega)
        rw [hcprev, hzt, pair_edgePt] at hRp
        have hgp := F.order (j - 1) j (by omega) (by omega) (by omega)
        have ht0 : 0 ≤ t := by
          by_contra hneg; push Not at hneg; nlinarith
        -- the next constraint gives `t ≤ sj`
        have hcnext : F.off δ (a₀, b₀) (j + 1) = pair (F.ρ (j + 1)) (F.vert δ (a₀, b₀) j) := by
          unfold off
          rcases Nat.lt_or_ge (F.k + 1) (j + 1) with hh | hh
          · rw [show min (j + 1) (F.k + 1) = j by omega]
          · rw [show min (j + 1) (F.k + 1) = j + 1 by omega, F.vert_succ δ (a₀, b₀) j (by omega),
              pair_self_edgePt]
        have hRn := hR (j + 1) (by omega) (by omega)
        rw [hcnext, hvj, hzt, pair_edgePt, pair_edgePt] at hRn
        have hgn := F.order j (j + 1) (by omega) (by omega) (by omega)
        have hcrn : cross (F.ρ (j + 1)) (F.ρ j) = -cross (F.ρ j) (F.ρ (j + 1)) := by
          simp only [cross]; ring
        have htle : t ≤ sj := by
          rw [hcrn] at hRn
          by_contra hgt; push Not at hgt; nlinarith
        have hnn := F.nonneg j (by omega)
        refine ⟨?_, ?_⟩
        · have hp := F.past_vert hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ (j - 1) (by omega) (by omega)
          have hmono := cross_logState_edgePt_mono (σ := F.ρ (j - 1)) hW1 hnn.1 hnn.2
            (F.nonneg (j - 1) (by omega)).1 (F.nonneg (j - 1) (by omega)).2 le_rfl ht0
            (by rw [← hzt]; exact hz2)
          have h0 : edgePt W (F.ρ j) 0 = W := by simp [edgePt]
          rw [h0] at hmono
          rw [hzt]; linarith
        · have hmono := cross_logState_edgePt_mono (σ := F.ρ (j + 1)) hW1 hnn.1 hnn.2
            (F.nonneg (j + 1) (by omega)).1 (F.nonneg (j + 1) (by omega)).2 ht0 htle
            (by rw [← hvj]; exact hVj2)
          rw [← hvj] at hmono
          rw [hzt]; linarith

theorem off_one : F.off δ (a₀, b₀) 1 = a₀ := by
  simp [off, F.ρ1, pair, show min 1 (F.k + 1) = 1 by omega, vert]

theorem off_two : F.off δ (a₀, b₀) 2 = pair (F.ρ 2) (a₀, b₀) := by
  unfold off
  rcases Nat.lt_or_ge (F.k + 1) 2 with hk | hk
  · rw [show min 2 (F.k + 1) = 1 by omega]; rfl
  · rw [show min 2 (F.k + 1) = 2 by omega,
      show (2 : ℕ) = 1 + 1 from rfl, F.vert_succ δ (a₀, b₀) 1 le_rfl, pair_self_edgePt]
    rfl

omit hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ in
theorem off_interior (j : ℕ) (hj2 : 2 ≤ j) (hjk : j ≤ F.k + 1) :
    F.off δ (a₀, b₀) j = pair (F.ρ j) (F.vert δ (a₀, b₀) (j - 1)) := by
  have := F.vert_succ δ (a₀, b₀) (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at this
  simp only [off, show min j (F.k + 1) = j by omega]; rw [this, pair_self_edgePt]

omit hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ in
theorem off_next (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ F.k + 1) :
    F.off δ (a₀, b₀) (j + 1) = pair (F.ρ (j + 1)) (F.vert δ (a₀, b₀) j) := by
  unfold off
  rcases Nat.lt_or_ge (F.k + 1) (j + 1) with hh | hh
  · rw [show min (j + 1) (F.k + 1) = j by omega]
  · rw [show min (j + 1) (F.k + 1) = j + 1 by omega, F.vert_succ δ (a₀, b₀) j hj1,
      pair_self_edgePt]

/-- **The band.**  For every edge, the half-margin goodness persists on `R_e` for small `e ≥ 0`. -/
theorem eventually_bandGood (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ F.k + 2) :
    ∀ᶠ e in nhds (0 : ℝ), 0 ≤ e → F.BandGood δ (F.off δ (a₀, b₀)) e j := by
  have hch := F.chain δ hδ ha₀ hb₀ hdepth hsmall hV1
  have hlog2δ : ∀ x, 0 < x → x ≤ Real.exp (-(2 * δ)) → Real.log x ≤ -(2 * δ) := fun x hx h => by
    calc Real.log x ≤ Real.log (Real.exp (-(2 * δ))) := Real.log_le_log hx h
      _ = _ := Real.log_exp _
  have hhalf : ∀ x : ℝ, 2 * (δ / 2) * x = δ * x := fun x => by ring
  rcases Nat.lt_or_ge j 2 with hj | hj
  · -- the vertical edge
    have hj1' : j = 1 := by omega
    subst hj1'
    have hρ22 : 0 < (F.ρ 2).2 := by
      have := F.order 1 2 le_rfl (by norm_num) (by omega)
      simpa [cross, F.ρ1] using this
    have hn2 := F.nonneg 2 (by omega)
    have hN2 := F.nrm_pos 2 (by omega)
    have h0 : -(F.ρ 2).1 * Real.log b₀ + (F.ρ 2).2 * Real.log a₀ < -(δ * nrm (F.ρ 2)) := by
      have := hV1; rw [cross_logState] at this
      have : 0 < δ * nrm (F.ρ 2) := by positivity
      simp only at *; linarith
    filter_upwards [eventually_logpair_lt (x1 := -((F.ρ 2).1 / (F.ρ 2).2)) (y1 := 1) hb₀ ha₀ h0,
      eventually_pos_affine (x1 := -((F.ρ 2).1 / (F.ρ 2).2)) hb₀] with e he hpos he0
    intro z hz1 hz2 hzb1 hzb2 hR hact
    rw [F.off_one hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ] at hact
    have hza : z.1 = a₀ + e * 1 := by simp [pair, F.ρ1] at hact; linarith
    have hR2 := hR 2 (by norm_num) (by omega)
    rw [F.off_two hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ] at hR2
    have hzb : b₀ + e * -((F.ρ 2).1 / (F.ρ 2).2) ≤ z.2 := by
      simp only [pair] at hR2
      rw [hza] at hR2
      have h1 : (F.ρ 2).2 * (b₀ + e * -((F.ρ 2).1 / (F.ρ 2).2)) = (F.ρ 2).2 * b₀ - e * (F.ρ 2).1 := by
        field_simp; ring
      have h2 : (F.ρ 2).2 * (b₀ + e * -((F.ρ 2).1 / (F.ρ 2).2)) ≤ (F.ρ 2).2 * z.2 := by
        rw [h1]; nlinarith
      exact le_of_mul_le_mul_left h2 hρ22
    refine ⟨?_, ?_⟩
    · rw [show (1 - 1 : ℕ) = 0 from rfl, F.ρ0, hhalf]
      simp only [cross, nrm, logState]
      have := hlog2δ z.2 hz2 hzb2; nlinarith
    · rw [show (1 + 1 : ℕ) = 2 from rfl, hhalf]
      have := cross_le_of_bounds (σ := F.ρ 2) (z := z) hn2.1 hn2.2 hz1 (le_of_eq hza) hpos hzb
      linarith
  · rcases Nat.lt_or_ge (F.k + 1) j with hjl | hjl
    · -- the horizontal edge
      have hjk2 : j = F.k + 2 := by omega
      subst hjk2
      set V := F.vert δ (a₀, b₀) (F.k + 1) with hV
      obtain ⟨hV1p, hV2p, -⟩ := hch (F.k + 1) (by omega) le_rfl
      have hρ1 : 0 < (F.ρ (F.k + 1)).1 := by
        have := F.order (F.k + 1) (F.k + 2) (by omega) (by omega) le_rfl
        simpa [cross, F.ρk2] using this
      have hn := F.nonneg (F.k + 1) (by omega)
      have hN := F.nrm_pos (F.k + 1) (by omega)
      have hp := F.past_vert hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ (F.k + 1) (by omega) le_rfl
      rw [← hV, cross_logState] at hp
      have h0 : δ * nrm (F.ρ (F.k + 1)) <
          -(F.ρ (F.k + 1)).1 * Real.log V.2 + (F.ρ (F.k + 1)).2 * Real.log V.1 := by
        have : 0 < δ * nrm (F.ρ (F.k + 1)) := by positivity
        linarith
      filter_upwards [eventually_logpair_gt (x1 := 1)
          (y1 := -((F.ρ (F.k + 1)).2 / (F.ρ (F.k + 1)).1)) hV2p hV1p h0,
        eventually_pos_affine (x1 := -((F.ρ (F.k + 1)).2 / (F.ρ (F.k + 1)).1)) hV1p]
        with e he hpos he0
      intro z hz1 hz2 hzb1 hzb2 hR hact
      have hcl : F.off δ (a₀, b₀) (F.k + 2) = V.2 := by
        simp [off, F.ρk2, pair, hV]
      rw [hcl] at hact
      have hzb : z.2 = V.2 + e * 1 := by simp [pair, F.ρk2] at hact; linarith
      have hck : F.off δ (a₀, b₀) (F.k + 1) = pair (F.ρ (F.k + 1)) V := by simp [off, hV]
      have hRk := hR (F.k + 1) (by omega) (by omega)
      rw [hck] at hRk
      have hza : V.1 + e * -((F.ρ (F.k + 1)).2 / (F.ρ (F.k + 1)).1) ≤ z.1 := by
        simp only [pair] at hRk
        rw [hzb] at hRk
        have h1 : (F.ρ (F.k + 1)).1 * (V.1 + e * -((F.ρ (F.k + 1)).2 / (F.ρ (F.k + 1)).1)) =
            (F.ρ (F.k + 1)).1 * V.1 - e * (F.ρ (F.k + 1)).2 := by field_simp; ring
        have h2 : (F.ρ (F.k + 1)).1 * (V.1 + e * -((F.ρ (F.k + 1)).2 / (F.ρ (F.k + 1)).1)) ≤
            (F.ρ (F.k + 1)).1 * z.1 := by rw [h1]; nlinarith
        exact le_of_mul_le_mul_left h2 hρ1
      refine ⟨?_, ?_⟩
      · rw [show F.k + 2 - 1 = F.k + 1 by omega, hhalf]
        have := cross_ge_of_bounds (σ := F.ρ (F.k + 1)) (z := z) hn.1 hn.2 hpos hza hz2
          (le_of_eq hzb)
        linarith
      · rw [show F.k + 2 + 1 = F.k + 3 by omega, F.ρk3, hhalf]
        simp only [cross, nrm, logState]
        have := hlog2δ z.1 hz1 hzb1; nlinarith
    · -- an interior edge
      set W := F.vert δ (a₀, b₀) (j - 1) with hW
      set V := F.vert δ (a₀, b₀) j with hV
      set sj := F.par δ (a₀, b₀) j with hsj
      have hint := F.interior j hj hjl
      have hvj : V = edgePt W (F.ρ j) sj := by
        have := F.vert_succ δ (a₀, b₀) (j - 1) (by omega)
        rwa [show j - 1 + 1 = j by omega] at this
      obtain ⟨hW1, hW2, -⟩ := hch (j - 1) (by omega) (by omega)
      obtain ⟨hVj1, hVj2, -, -, -, -, hnext⟩ := hch j (by omega) hjl
      have hpm := F.past_vert hδ ha₀ hb₀ hdepth hsmall hV1 hb2δ (j - 1) (by omega) (by omega)
      rw [← hW, cross_logState] at hpm
      rw [← hV, cross_logState] at hnext
      set ρ := F.ρ j with hρ
      set ρm := F.ρ (j - 1) with hρm
      set ρp := F.ρ (j + 1) with hρp
      have hgm : 0 < cross ρm ρ := F.order (j - 1) j (by omega) (by omega) (by omega)
      have hgp : 0 < cross ρ ρp := F.order j (j + 1) (by omega) (by omega) (by omega)
      have hnm := F.nonneg (j - 1) (by omega)
      have hnp := F.nonneg (j + 1) (by omega)
      have hNm := F.nrm_pos (j - 1) (by omega)
      have hNp := F.nrm_pos (j + 1) (by omega)
      set gm := cross ρm ρ with hgmdef
      set gp := cross ρ ρp with hgpdef
      have h0m : δ * nrm ρm < -ρm.1 * Real.log W.2 + ρm.2 * Real.log W.1 := by
        have : 0 < δ * nrm ρm := by positivity
        linarith
      have h0p : -ρp.1 * Real.log V.2 + ρp.2 * Real.log V.1 < -(δ * nrm ρp) := by
        have : 0 < δ * nrm ρp := by positivity
        linarith
      filter_upwards [
        eventually_logpair_gt (x1 := (1 + ρ.1 * ρm.2 / gm) / ρ.2) (y1 := -(ρm.2 / gm))
          hW2 hW1 h0m,
        eventually_pos_affine (x1 := -(ρm.2 / gm)) hW1,
        eventually_logpair_lt (x1 := (1 - ρ.1 * ρp.2 / gp) / ρ.2) (y1 := ρp.2 / gp)
          hVj2 hVj1 h0p,
        eventually_pos_affine (x1 := (1 - ρ.1 * ρp.2 / gp) / ρ.2) hVj2]
        with e hem hposm hep hposp he0
      intro z hz1 hz2 hzb1 hzb2 hR hact
      rw [F.off_interior j hj hjl] at hact
      have hRm := hR (j - 1) (by omega) (by omega)
      have hcm : F.off δ (a₀, b₀) (j - 1) = pair ρm W := by
        simp only [off, show min (j - 1) (F.k + 1) = j - 1 by omega, hW, hρm]
      rw [hcm] at hRm
      have hRp := hR (j + 1) (by omega) (by omega)
      rw [F.off_next j (by omega) hjl] at hRp
      have hpairV : pair ρ V = pair ρ W := by rw [hvj, pair_self_edgePt]
      simp only [pair] at hact hRm hRp hpairV
      -- lower bounds from the previous constraint
      set x := z.1 - W.1 with hx
      set y := z.2 - W.2 with hy
      have hE : ρ.1 * x + ρ.2 * y = e := by rw [hx, hy]; linarith
      have hIm : e ≤ ρm.1 * x + ρm.2 * y := by rw [hx, hy]; linarith
      have hgmx : -(ρm.2 * e) ≤ gm * x := by
        have h1 := mul_le_mul_of_nonneg_left hIm hint.2.le
        have h2 : ρm.2 * (ρ.1 * x + ρ.2 * y) = ρm.2 * e := by rw [hE]
        have h3 : 0 ≤ ρ.2 * e := mul_nonneg hint.2.le he0
        have key : gm * x = ρ.2 * (ρm.1 * x + ρm.2 * y) - ρm.2 * (ρ.1 * x + ρ.2 * y) := by
          simp only [hgmdef, cross]; ring
        rw [key, h2]; linarith
      have hxlo : W.1 + e * -(ρm.2 / gm) ≤ z.1 := by
        have : e * -(ρm.2 / gm) ≤ x := by
          rw [show e * -(ρm.2 / gm) = -(ρm.2 * e) / gm by ring, div_le_iff₀ hgm]; linarith
        linarith
      have hyhi : z.2 ≤ W.2 + e * ((1 + ρ.1 * ρm.2 / gm) / ρ.2) := by
        have hxlo' : -(ρm.2 * e) / gm ≤ x := by rw [div_le_iff₀ hgm]; linarith
        have : ρ.2 * y ≤ ρ.2 * (e * ((1 + ρ.1 * ρm.2 / gm) / ρ.2)) := by
          have hexp : ρ.2 * (e * ((1 + ρ.1 * ρm.2 / gm) / ρ.2)) = e + ρ.1 * (ρm.2 * e / gm) := by
            have : ρ.2 ≠ 0 := hint.2.ne'
            have : gm ≠ 0 := hgm.ne'
            field_simp
          rw [hexp]
          have : -(ρ.1 * x) ≤ ρ.1 * (ρm.2 * e / gm) := by
            have := mul_le_mul_of_nonneg_left hxlo' hint.1.le
            rw [show ρ.1 * (-(ρm.2 * e) / gm) = -(ρ.1 * (ρm.2 * e / gm)) by ring] at this
            linarith
          linarith
        have := le_of_mul_le_mul_left this hint.2
        linarith
      -- upper bounds from the next constraint
      set x' := z.1 - V.1 with hx'
      set y' := z.2 - V.2 with hy'
      have hE' : ρ.1 * x' + ρ.2 * y' = e := by rw [hx', hy']; linarith
      have hIp : e ≤ ρp.1 * x' + ρp.2 * y' := by rw [hx', hy']; linarith
      have hgpx : gp * x' ≤ ρp.2 * e := by
        have h1 := mul_le_mul_of_nonneg_left hIp hint.2.le
        have h2 : ρp.2 * (ρ.1 * x' + ρ.2 * y') = ρp.2 * e := by rw [hE']
        have h3 : 0 ≤ ρ.2 * e := mul_nonneg hint.2.le he0
        have key : gp * x' = ρp.2 * (ρ.1 * x' + ρ.2 * y') - ρ.2 * (ρp.1 * x' + ρp.2 * y') := by
          simp only [hgpdef, cross]; ring
        rw [key, h2]; linarith
      have hxhi : z.1 ≤ V.1 + e * (ρp.2 / gp) := by
        have : x' ≤ e * (ρp.2 / gp) := by
          rw [show e * (ρp.2 / gp) = ρp.2 * e / gp by ring, le_div_iff₀ hgp]; linarith
        linarith
      have hylo : V.2 + e * ((1 - ρ.1 * ρp.2 / gp) / ρ.2) ≤ z.2 := by
        have hxhi' : x' ≤ ρp.2 * e / gp := by rw [le_div_iff₀ hgp]; linarith
        have : ρ.2 * (e * ((1 - ρ.1 * ρp.2 / gp) / ρ.2)) ≤ ρ.2 * y' := by
          have hexp : ρ.2 * (e * ((1 - ρ.1 * ρp.2 / gp) / ρ.2)) = e - ρ.1 * (ρp.2 * e / gp) := by
            have : ρ.2 ≠ 0 := hint.2.ne'
            have : gp ≠ 0 := hgp.ne'
            field_simp
          rw [hexp]
          have := mul_le_mul_of_nonneg_left hxhi' hint.1.le
          linarith
        have := le_of_mul_le_mul_left this hint.2
        linarith
      refine ⟨?_, ?_⟩
      · rw [hhalf]
        have := cross_ge_of_bounds (σ := ρm) (z := z) hnm.1 hnm.2 hposm hxlo hz2 hyhi
        linarith
      · rw [hhalf]
        have := cross_le_of_bounds (σ := ρp) (z := z) hnp.1 hnp.2 hz1 hxhi hposp hylo
        linarith

end Polygon

/-- **Existence of the polygon at every small scale.**  With the top-left vertex
`(b₀ ^ K, b₀)` the polygon exists for every `b₀ ∈ (0, β₀]`. -/
theorem exists_polygon {δ : ℝ} (hδ : 0 < δ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ K : ℕ, 1 ≤ K ∧ ∀ b₀ : ℝ, 0 < b₀ → b₀ ≤ β₀ →
      (∀ j, 1 ≤ j → j ≤ F.k + 2 → 0 < F.off δ (b₀ ^ K, b₀) j) ∧
      (∀ z : ℝ × ℝ, b₀ ^ K ≤ z.1 → b₀ ≤ z.2 → F.InR (F.off δ (b₀ ^ K, b₀)) z) ∧
      (∀ z : ℝ × ℝ, 0 < z.1 → 0 < z.2 → z.1 ≤ Real.exp (-(2 * δ)) →
        z.2 ≤ Real.exp (-(2 * δ)) → F.InR (F.off δ (b₀ ^ K, b₀)) z →
        ∀ j, 1 ≤ j → j ≤ F.k + 2 → pair (F.ρ j) z = F.off δ (b₀ ^ K, b₀) j →
          Good δ (F.ρ (j - 1)) (F.ρ (j + 1)) (logState z)) := by
  have hρ22 : 0 < (F.ρ 2).2 := by
    have := F.order 1 2 le_rfl (by norm_num) (by omega)
    simpa [cross, F.ρ1] using this
  have hρ21 : 0 ≤ (F.ρ 2).1 := (F.nonneg 2 (by omega)).1
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
  exact F.polygon hδ ha₀ hb₀ hdepth hsmall hV1 hb2

end Rays

end PlanarZSH
end CRNT
