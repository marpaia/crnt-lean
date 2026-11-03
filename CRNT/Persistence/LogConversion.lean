import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# From tail sums to log-ratio coordinates

With `a = -log ε`, a coordinate `Y` whose tail sum `U` (`Y ≤ U ≤ K Y`) satisfies `ε ^ h ≤ 2U`
has `log Y / log z₀ ≤ h + E`, and `U ≤ 2 ε ^ h` gives `h - E ≤ log Y / log z₀`, whenever the
reference coordinate `z₀` lies in `[ε / C, 2ε]`; the error is
`E = (H (log 2 + log C) + log (2K) + log 2) / (a - log 2)` for `0 ≤ h ≤ H`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Real

/-- The conversion error. -/
noncomputable def convErr (H C K a : ℝ) : ℝ :=
  (H * (log 2 + log C) + log (2 * K) + log 2) / (a - log 2)

theorem log_z0_bounds {ε C z0 : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) (h1 : ε / C ≤ z0) (h2 : z0 ≤ 2 * ε) :
    -log ε - log 2 ≤ -log z0 ∧ -log z0 ≤ -log ε + log C := by
  have hz0 : 0 < z0 := lt_of_lt_of_le (div_pos hε (by linarith)) h1
  constructor
  · have := log_le_log hz0 h2
    rw [log_mul (by norm_num) hε.ne'] at this; linarith
  · have := log_le_log (div_pos hε (by linarith)) h1
    rw [log_div hε.ne' (by linarith)] at this; linarith

theorem conv_up {ε C K H h z0 Y U : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (ha : log 2 < -log ε) (h1 : ε / C ≤ z0) (h2 : z0 ≤ 2 * ε) (hY : 0 < Y) (hUY : U ≤ K * Y)
    (hh0 : 0 ≤ h) (hhH : h ≤ H) (hup : ε ^ h ≤ 2 * U) :
    log Y / log z0 ≤ h + convErr H C K (-log ε) := by
  set a := -log ε with hadef
  obtain ⟨hz1, _⟩ := log_z0_bounds hε hC h1 h2
  have hpos : 0 < a - log 2 := by linarith
  have hz0pos : 0 < -log z0 := by linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2K : 0 < log (2 * K) := log_pos (by linarith)
  have hlogC : 0 ≤ log C := log_nonneg hC
  -- `-log Y ≤ h a + log (2K)`
  have hYb : -log Y ≤ h * a + log (2 * K) := by
    have hεh : ε ^ h = exp (h * log ε) := by rw [rpow_def_of_pos hε]; ring_nf
    have : ε ^ h ≤ 2 * K * Y := le_trans hup (by linarith)
    have hlog := log_le_log (by rw [hεh]; exact exp_pos _) this
    rw [hεh, log_exp, log_mul (by positivity) hY.ne'] at hlog
    rw [hadef]; linarith
  have hX : 0 ≤ h * a + log (2 * K) := by nlinarith
  have e1 : log Y / log z0 = -log Y / -log z0 := by rw [neg_div_neg_eq]
  rw [e1]
  calc -log Y / -log z0 ≤ (h * a + log (2 * K)) / -log z0 :=
        div_le_div_of_nonneg_right hYb hz0pos.le
    _ ≤ (h * a + log (2 * K)) / (a - log 2) := div_le_div_of_nonneg_left hX hpos hz1
    _ = h + (h * log 2 + log (2 * K)) / (a - log 2) := by field_simp; ring
    _ ≤ h + convErr H C K a := by
        unfold convErr
        have : (h * log 2 + log (2 * K)) / (a - log 2) ≤
            (H * (log 2 + log C) + log (2 * K) + log 2) / (a - log 2) :=
          div_le_div_of_nonneg_right (by nlinarith) hpos.le
        linarith

theorem conv_down {ε C K H h z0 Y U : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (ha : log 2 < -log ε) (h1 : ε / C ≤ z0) (h2 : z0 ≤ 2 * ε) (hY : 0 < Y) (hYU : Y ≤ U)
    (hh0 : 0 ≤ h) (hhH : h ≤ H) (hdown : U ≤ 2 * ε ^ h) :
    h - convErr H C K (-log ε) ≤ log Y / log z0 := by
  set a := -log ε with hadef
  obtain ⟨hz1, hz2⟩ := log_z0_bounds hε hC h1 h2
  have hpos : 0 < a - log 2 := by linarith
  have hz0pos : 0 < -log z0 := by linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlog2K : 0 < log (2 * K) := log_pos (by linarith)
  have hlogC : 0 ≤ log C := log_nonneg hC
  have hYb : h * a - log 2 ≤ -log Y := by
    have hεh : ε ^ h = exp (h * log ε) := by rw [rpow_def_of_pos hε]; ring_nf
    have : Y ≤ 2 * ε ^ h := le_trans hYU hdown
    have hlog := log_le_log hY this
    rw [log_mul (by norm_num) (by rw [hεh]; exact (exp_pos _).ne'), hεh, log_exp] at hlog
    rw [hadef]; linarith
  have e1 : log Y / log z0 = -log Y / -log z0 := by rw [neg_div_neg_eq]
  rw [e1]
  have hE : log 2 / (a - log 2) ≤ convErr H C K a := by
    unfold convErr
    apply div_le_div_of_nonneg_right _ hpos.le
    nlinarith
  have hstep : (h * a - log 2) / -log z0 ≤ -log Y / -log z0 :=
    div_le_div_of_nonneg_right hYb hz0pos.le
  rcases le_or_gt 0 (h * a - log 2) with hX | hX
  · have hden : 0 < a + log C := by linarith
    have h3 : (h * a - log 2) / (a + log C) ≤ (h * a - log 2) / -log z0 :=
      div_le_div_of_nonneg_left hX hz0pos hz2
    have h4 : h - (h * log C + log 2) / (a + log C) = (h * a - log 2) / (a + log C) := by
      field_simp; ring
    have h5 : (h * log C + log 2) / (a + log C) ≤ convErr H C K a := by
      unfold convErr
      calc (h * log C + log 2) / (a + log C) ≤ (h * log C + log 2) / (a - log 2) :=
            div_le_div_of_nonneg_left (by nlinarith) hpos (by linarith)
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hpos.le
    linarith
  · have h3 : (h * a - log 2) / (a - log 2) ≤ (h * a - log 2) / -log z0 := by
      rw [div_le_div_iff₀ hpos hz0pos]; nlinarith
    have h4 : (h * a - log 2) / (a - log 2) = h + (h * log 2 - log 2) / (a - log 2) := by
      field_simp; ring
    have h5 : -(log 2 / (a - log 2)) ≤ (h * log 2 - log 2) / (a - log 2) := by
      rw [← neg_div]; apply div_le_div_of_nonneg_right _ hpos.le; nlinarith
    linarith

end Persistence
end CRNT
