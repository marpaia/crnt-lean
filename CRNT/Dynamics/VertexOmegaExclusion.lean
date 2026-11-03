import CRNT.Dynamics.OrbitRegularity
import CRNT.Dynamics.GenuineConfinement

/-!
# Vertices of a compatibility class are not ω-limit points

Craciun, Dickenstein, Shiu, Sturmfels, *Toric dynamical systems*, J. Symb. Comput. 44 (2009),
Proposition 20 (see also Anderson, SIAM J. Appl. Math. 68 (2008), Theorem 3.7): for a
complex-balanced system, a vertex of a stoichiometric compatibility class is never an ω-limit
point of a positive trajectory.

**Vertex.**  A nonnegative point `w` with zero set `P` is a vertex of its class when no nonzero
stoichiometric vector vanishes on `P` (`IsVertexZeroSet`); the face `{x in the class : x_P = 0}`
is then the single point `w`.

**Argument.**  The relative entropy `E = relEntropy xstar` has a strict local maximum at a vertex
along the class (`relEntropy_lt_near_vertex`).  Writing `y = w + u` with `u` stoichiometric,
the tangent-line form of Gibbs' inequality gives `E y - E w ≤ ∑ s, log (y s / xstar s) * u s`.
On `P` the factor `log (y s / xstar s)` tends to `-∞` while `u s = y s > 0`, and off `P` it is
bounded; the vertex condition makes `∑_{s ∈ P} u s` control `‖u‖`
(`exists_norm_le_sum_zeroSet`).  Since `E` decreases along the orbit, orbit points near an
ω-point `w` have `E ≥ E w`, which contradicts the strict maximum (`false_of_vertex_omegaPoint`).

Nothing here is an axiom or a `sorry`.
-/

open scoped NNReal Topology
open Filter Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The zero set `P` cuts the class down to one point: no nonzero stoichiometric vector vanishes
on `P`. -/
def IsVertexZeroSet (N : Network S) (P : Finset S) : Prop :=
  ∀ u ∈ N.stoichSubspace, (∀ s ∈ P, u s = 0) → u = 0

/-- **Norm control on a vertex.** -/
theorem exists_norm_le_sum_zeroSet (N : Network S) {P : Finset S} (hP : N.IsVertexZeroSet P) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ N.stoichSubspace, m * ‖u‖ ≤ ∑ s ∈ P, |u s| := by
  classical
  set V := N.stoichSubspace with hV
  set K : Set (Concentration S) := Metric.sphere (0 : Concentration S) 1 ∩ (V : Set _) with hK
  have hVclosed : IsClosed (V : Set (Concentration S)) := Submodule.closed_of_finiteDimensional V
  have hKc : IsCompact K := (isCompact_sphere _ _).inter_right hVclosed
  have hq : Continuous fun u : Concentration S => ∑ s ∈ P, |u s| :=
    continuous_finsetSum _ fun s _ => (continuous_apply s).abs
  have hhom : ∀ u : Concentration S, ∀ c : ℝ, 0 ≤ c →
      ∑ s ∈ P, |(c • u) s| = c * ∑ s ∈ P, |u s| := by
    intro u c hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [abs_mul, abs_of_nonneg hc]
  by_cases hKne : K.Nonempty
  · obtain ⟨u₀, hu₀K, hmin⟩ := hKc.exists_isMinOn hKne hq.continuousOn
    have hu₀V : u₀ ∈ V := hu₀K.2
    have hu₀n : ‖u₀‖ = 1 := by simpa using hu₀K.1
    have hpos : 0 < ∑ s ∈ P, |u₀ s| := by
      rcases (Finset.sum_nonneg fun s _ => abs_nonneg (u₀ s)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : ∀ s ∈ P, u₀ s = 0 := by
          intro s hs
          have := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => abs_nonneg (u₀ s)).mp h.symm s hs
          exact abs_eq_zero.mp this
        have := hP u₀ hu₀V hz
        rw [this, norm_zero] at hu₀n
        exact zero_ne_one hu₀n
    refine ⟨_, hpos, fun u hu => ?_⟩
    by_cases hu0 : u = 0
    · subst hu0; simp only [norm_zero, mul_zero]
      exact Finset.sum_nonneg fun s _ => abs_nonneg _
    · have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have hmem : ‖u‖⁻¹ • u ∈ K := by
        refine ⟨?_, V.smul_mem _ hu⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnpos.ne']
      have hle : ∑ s ∈ P, |u₀ s| ≤ ∑ s ∈ P, |(‖u‖⁻¹ • u) s| := hmin hmem
      rw [hhom u _ (inv_nonneg.mpr hnpos.le)] at hle
      have := mul_le_mul_of_nonneg_left hle hnpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul, mul_comm] at this
  · refine ⟨1, one_pos, fun u hu => ?_⟩
    by_cases hu0 : u = 0
    · subst hu0; simp only [norm_zero, mul_zero]
      exact Finset.sum_nonneg fun s _ => abs_nonneg _
    · exfalso
      apply hKne
      have hnpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      refine ⟨‖u‖⁻¹ • u, ?_, V.smul_mem _ hu⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnpos.ne']

/-- **Tangent-line form of Gibbs' inequality, per coordinate.** -/
theorem relEntropyTerm_sub_le {w z a : ℝ} (hw : 0 ≤ w) (hz : 0 < z) (ha : 0 < a) :
    (z * Real.log (z / a) - z + a) - (w * Real.log (w / a) - w + a) ≤
      Real.log (z / a) * (z - w) := by
  rcases eq_or_lt_of_le hw with h | hw'
  · subst h
    simp only [zero_mul, zero_div, Real.log_zero, sub_zero]
    nlinarith
  · have hg := relEntropyTerm_nonneg (t := w) (a := z) hw hz
    have h1 : Real.log (w / z) = Real.log (w / a) - Real.log (z / a) := by
      rw [Real.log_div hw'.ne' hz.ne', Real.log_div hw'.ne' ha.ne', Real.log_div hz.ne' ha.ne']
      ring
    rw [h1] at hg
    nlinarith

/-- **Relative entropy is a strict local maximum at a vertex, along the class.** -/
theorem relEntropy_lt_near_vertex (N : Network S) {xstar : Concentration S}
    (hxs : xstar.Positive) {w : Concentration S} (hwnn : Concentration.Nonnegative w)
    {P : Finset S} (hzero : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty)
    (hvert : N.IsVertexZeroSet P) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : Concentration S, y.Positive → (y - w) ∈ N.stoichSubspace →
      dist y w < ρ → relEntropy xstar y < relEntropy xstar w := by
  classical
  obtain ⟨m, hm, hnorm⟩ := N.exists_norm_le_sum_zeroSet hvert
  -- constants
  set A : ℝ := ∑ s, |Real.log (xstar s)| with hA
  set B : ℝ := ∑ s, (|Real.log (w s / 2)| + |Real.log (3 * w s / 2)|) + A with hB
  set n : ℝ := (Fintype.card S : ℝ) with hn
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun s _ => abs_nonneg _
  have hB0 : 0 ≤ B := add_nonneg (Finset.sum_nonneg fun s _ =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)) hA0
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set ρ₁ : ℝ := Real.exp (-(A + n * B / m) - 1) with hρ₁
  -- the positive coordinates of `w`
  set Q : Finset S := Finset.univ.filter (fun s => s ∉ P) with hQ
  have hwQ : ∀ s ∈ Q, 0 < w s := by
    intro s hs
    have hsP : s ∉ P := (Finset.mem_filter.mp hs).2
    rcases (hwnn s).lt_or_eq with h | h
    · exact h
    · exact absurd ((hzero s).mpr h.symm) hsP
  set ρ₂ : ℝ := if hQne : Q.Nonempty then Q.inf' hQne (fun s => w s / 2) else 1 with hρ₂
  have hρ₂pos : 0 < ρ₂ := by
    rw [hρ₂]
    split_ifs with hQne
    · rw [Finset.lt_inf'_iff]
      intro s hs
      exact half_pos (hwQ s hs)
    · exact one_pos
  have hρ₂le : ∀ s ∈ Q, ρ₂ ≤ w s / 2 := by
    intro s hs
    rw [hρ₂, dif_pos ⟨s, hs⟩]
    exact Finset.inf'_le _ hs
  refine ⟨min ρ₁ ρ₂, lt_min (Real.exp_pos _) hρ₂pos, ?_⟩
  intro y hy hyw hdist
  set u : Concentration S := y - w with hu
  have hnu : ‖u‖ < min ρ₁ ρ₂ := by rwa [← dist_eq_norm]
  have hcoord : ∀ s, |u s| ≤ ‖u‖ := fun s => by
    have := norm_le_pi_norm u s
    rwa [Real.norm_eq_abs] at this
  -- Gibbs: `E y - E w ≤ ∑ log(y/x*) * u`
  have hstep : relEntropy xstar y - relEntropy xstar w ≤
      ∑ s, Real.log (y s / xstar s) * u s := by
    unfold relEntropy
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    have := relEntropyTerm_sub_le (hwnn s) (hy s) (hxs s)
    simpa [hu] using this
  -- split over `P` and its complement
  have hsplit : ∑ s, Real.log (y s / xstar s) * u s =
      ∑ s ∈ P, Real.log (y s / xstar s) * u s + ∑ s ∈ Q, Real.log (y s / xstar s) * u s := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.univ) (fun s => s ∈ P)
      (fun s => Real.log (y s / xstar s) * u s)
    have hPf : Finset.univ.filter (fun s => s ∈ P) = P := by ext; simp
    rw [hPf] at h
    rw [hQ, h]
  -- on `P`: `u s = y s ∈ (0, ρ₁)`
  set q : ℝ := ∑ s ∈ P, |u s| with hq
  have huP : ∀ s ∈ P, u s = y s := by
    intro s hs; simp [hu, (hzero s).mp hs]
  have hqpos : 0 < q := by
    obtain ⟨s₀, hs₀⟩ := hPne
    have : 0 < |u s₀| := by rw [huP s₀ hs₀, abs_of_pos (hy s₀)]; exact hy s₀
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun s => |u s|)
      (fun s _ => abs_nonneg _) hs₀)
  have hP_le : ∑ s ∈ P, Real.log (y s / xstar s) * u s ≤ (Real.log ρ₁ + A) * q := by
    rw [hq, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    rw [huP s hs, abs_of_pos (hy s)]
    have hys : y s < ρ₁ := by
      have h1 := hcoord s
      rw [huP s hs, abs_of_pos (hy s)] at h1
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hnu (min_le_left _ _))
    have hlog : Real.log (y s / xstar s) ≤ Real.log ρ₁ + A := by
      rw [Real.log_div (hy s).ne' (hxs s).ne']
      have h1 : Real.log (y s) ≤ Real.log ρ₁ := Real.log_le_log (hy s) hys.le
      have h2 : -Real.log (xstar s) ≤ A := by
        have := Finset.single_le_sum (f := fun s => |Real.log (xstar s)|)
          (fun s _ => abs_nonneg _) (Finset.mem_univ s)
        exact le_trans (neg_le_abs _) this
      linarith
    nlinarith [hy s]
  -- off `P`: bounded logarithms
  have hQ_le : ∑ s ∈ Q, Real.log (y s / xstar s) * u s ≤ n * B * ‖u‖ := by
    have hterm : ∀ s ∈ Q, Real.log (y s / xstar s) * u s ≤ B * ‖u‖ := by
      intro s hs
      have hws := hwQ s hs
      have hus : |u s| ≤ w s / 2 :=
        (hcoord s).trans ((lt_of_lt_of_le hnu (min_le_right _ _)).le.trans (hρ₂le s hs))
      have hys_eq : y s = w s + u s := by simp [hu]
      have hlo : w s / 2 ≤ y s := by
        rw [hys_eq]; have := neg_abs_le (u s); linarith
      have hhi : y s ≤ 3 * w s / 2 := by
        rw [hys_eq]; have := le_abs_self (u s); linarith
      have hlogy : |Real.log (y s)| ≤ |Real.log (w s / 2)| + |Real.log (3 * w s / 2)| := by
        rw [abs_le]
        have hl1 : Real.log (w s / 2) ≤ Real.log (y s) := Real.log_le_log (by positivity) hlo
        have hl2 : Real.log (y s) ≤ Real.log (3 * w s / 2) := Real.log_le_log (hy s) hhi
        constructor
        · have := neg_abs_le (Real.log (w s / 2))
          have := abs_nonneg (Real.log (3 * w s / 2))
          linarith
        · have := le_abs_self (Real.log (3 * w s / 2))
          have := abs_nonneg (Real.log (w s / 2))
          linarith
      have hlog : |Real.log (y s / xstar s)| ≤ B := by
        rw [Real.log_div (hy s).ne' (hxs s).ne']
        have h1 : |Real.log (y s) - Real.log (xstar s)| ≤
            |Real.log (y s)| + |Real.log (xstar s)| := abs_sub _ _
        have h2 : |Real.log (w s / 2)| + |Real.log (3 * w s / 2)| ≤
            ∑ s, (|Real.log (w s / 2)| + |Real.log (3 * w s / 2)|) :=
          Finset.single_le_sum (f := fun s => |Real.log (w s / 2)| + |Real.log (3 * w s / 2)|)
            (fun s _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ s)
        have h3 : |Real.log (xstar s)| ≤ A :=
          Finset.single_le_sum (f := fun s => |Real.log (xstar s)|)
            (fun s _ => abs_nonneg _) (Finset.mem_univ s)
        rw [hB]; linarith
      calc Real.log (y s / xstar s) * u s ≤ |Real.log (y s / xstar s) * u s| := le_abs_self _
        _ = |Real.log (y s / xstar s)| * |u s| := abs_mul _ _
        _ ≤ B * ‖u‖ := mul_le_mul hlog (hcoord s) (abs_nonneg _) hB0
    calc ∑ s ∈ Q, Real.log (y s / xstar s) * u s ≤ ∑ s ∈ Q, B * ‖u‖ := Finset.sum_le_sum hterm
      _ = (Q.card : ℝ) * (B * ‖u‖) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * (B * ‖u‖) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB0 (norm_nonneg _))
          rw [hn]; exact_mod_cast Finset.card_le_univ Q
      _ = n * B * ‖u‖ := by ring
  have hmnorm : m * ‖u‖ ≤ q := hnorm u hyw
  have hnormq : ‖u‖ ≤ q / m := by rw [le_div_iff₀ hm]; linarith
  have hlogρ : Real.log ρ₁ = -(A + n * B / m) - 1 := by rw [hρ₁, Real.log_exp]
  have hfinal : relEntropy xstar y - relEntropy xstar w ≤ -q := by
    have hQ' : ∑ s ∈ Q, Real.log (y s / xstar s) * u s ≤ n * B * (q / m) :=
      hQ_le.trans (mul_le_mul_of_nonneg_left hnormq (mul_nonneg hn0 hB0))
    have : relEntropy xstar y - relEntropy xstar w ≤
        (Real.log ρ₁ + A) * q + n * B * (q / m) := by linarith
    rw [hlogρ] at this
    have heq : (-(A + n * B / m) - 1 + A) * q + n * B * (q / m) = -q := by
      field_simp
      ring
    linarith
  linarith

/-- **A vertex of the compatibility class is not an ω-limit point** (CDSS 2009, Prop. 20). -/
theorem false_of_vertex_omegaPoint (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {w : Concentration S} (hw : w ∈ omegaLimit atTop ϕ {x₀})
    (hwnn : Concentration.Nonnegative w) (hwaff : (w - x₀ : Concentration S) ∈ N.stoichSubspace)
    {P : Finset S} (hzero : ∀ s, s ∈ P ↔ w s = 0) (hPne : P.Nonempty)
    (hvert : N.IsVertexZeroSet P) : False := by
  obtain ⟨ρ, hρ, hmax⟩ := N.relEntropy_lt_near_vertex hxs hwnn hzero hPne hvert
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ (0 : ℝ≥0)
    rw [NNReal.coe_zero] at h
    exact h.symm.trans (ϕ.map_zero_apply x₀)
  have hpos : ∀ t : ℝ, 0 ≤ t → (γ x₀ t).Positive :=
    N.genuineOrbit_pos κ (by rw [hγ0]; exact hx₀) hsol
  -- an orbit point inside the ball
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ≥0, ϕ t₀ x₀ ∈ Metric.ball w ρ := by
    have hfreq := (mem_omegaLimit_iff_frequently (f := atTop) (ϕ := fun t x => ϕ t x)
      (s := {x₀}) w).mp hw (Metric.ball w ρ) (Metric.ball_mem_nhds w hρ)
    obtain ⟨t, ⟨x, hx, hxt⟩⟩ := hfreq.exists
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨t, hxt⟩
  have hy := hpos t₀ t₀.coe_nonneg
  rw [hϕγ] at ht₀
  have hcompat : (γ x₀ t₀ - w) ∈ N.stoichSubspace := by
    have h1 := N.stoichCompatible_of_forward_solution κ hsol t₀ t₀.coe_nonneg
    rw [hγ0] at h1
    have : γ x₀ t₀ - w = (γ x₀ t₀ - x₀) - (w - x₀) := by abel
    rw [this]
    exact N.stoichSubspace.sub_mem h1 hwaff
  have hlt := hmax _ hy hcompat (Metric.mem_ball.mp ht₀)
  -- Lyapunov descent from time `t₀` puts `w` below `E (γ x₀ t₀)`
  have hle : relEntropy xstar w ≤ relEntropy xstar (γ x₀ t₀) := by
    set Γ : ℝ → Concentration S := fun τ => γ x₀ (t₀ + τ) with hΓ
    have hΓd : ∀ τ, 0 ≤ τ → HasDerivAt Γ (N.massActionVectorField κ (Γ τ)) τ := by
      intro τ hτ
      have := (hsol (t₀ + τ) (by positivity)).comp_const_add (t₀ : ℝ) τ
      simpa [hΓ] using this
    have hΓpos : ∀ τ, 0 ≤ τ → (Γ τ).Positive := fun τ hτ => hpos _ (by positivity)
    have hdesc := N.genuineOrbit_relEntropy_le κ hxs hcb hΓpos hΓd
    have himg : Set.image2 (fun t x => ϕ t x) (Set.Ici t₀) {x₀} ⊆
        {y : Concentration S | relEntropy xstar y ≤ relEntropy xstar (γ x₀ t₀)} := by
      rintro y ⟨t, ht, x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp only [Set.mem_setOf_eq]
      rw [hϕγ]
      have hτ : (0 : ℝ) ≤ (t : ℝ) - t₀ := sub_nonneg.mpr (by exact_mod_cast ht)
      have := hdesc _ hτ
      simpa [hΓ] using this
    have hclosed : IsClosed {y : Concentration S |
        relEntropy xstar y ≤ relEntropy xstar (γ x₀ t₀)} :=
      isClosed_le (relEntropy_continuous hxs) continuous_const
    exact ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := fun t x => ϕ t x) (s := {x₀})
      (u := Set.Ici t₀) (Filter.Ici_mem_atTop t₀)).trans
        ((IsClosed.closure_subset_iff hclosed).mpr himg)) hw
  linarith

end Network
end CRNT
