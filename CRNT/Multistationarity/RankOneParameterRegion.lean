import CRNT.Dynamics.MassActionField
import CRNT.Equilibria.CompatibilityClass
import CRNT.Equilibria.SteadyState
import CRNT.Kinetics.MassActionJacobian
import CRNT.Analysis.NegDerivAtZeros

/-!
# Parameter regions for multistationarity: rank-one networks

Conradi–Feliu–Mincheva–Wiuf ("Identifying parameter regions for multistationarity", PLoS Comput.
Biol. 13, 2017, Theorem 1) decide, for a fixed rate vector `κ` and a fixed compatibility class,
whether there are one or several positive steady states, from the sign of a Jacobian determinant at
the positive steady states. Their hypotheses: the class is compact (the network is dissipative)
and contains no boundary steady state. Their conclusion, for a stoichiometric subspace of dimension
`s`: if the sign is `(-1)^s` at every positive steady state of the class, there is exactly one;
if it is `(-1)^{s+1}` at one of them, there are several. The set of `κ` at which the second case
occurs is the *parameter region for multistationarity*.

This module proves the theorem when the stoichiometric subspace is a line `span {v}` and `v` has a
positive and a negative entry (so every class is a compact segment). The class of a positive `x₀`
is `{x₀ + t • v}` for `t` in a closed interval `[t₋, t₊]`, and the field along it is
`F(x₀ + t • v) = φ(t) • v` with `φ = lineField κ x₀ v i₀` (`i₀` any coordinate with `v i₀ ≠ 0`).
The Jacobian determinant of Conradi et al. has the sign of `-φ'(t)`, so their sign `(-1)^1` is
`φ' < 0`.

* `rankOne_lineField_left_pos`, `rankOne_lineField_right_neg`: at the two boundary points of the
  class, `φ > 0` and `φ < 0` (the field points into the class; no boundary steady state).
* `rankOne_exists_positive_steadyState`: there is a positive steady state in the class.
* `rankOne_three_steadyStates_of_deriv_pos`: a positive steady state with `φ' > 0` is flanked by
  two more, one on each side: at least three positive steady states.
* `rankOne_existsUnique_of_deriv_neg`: if `φ' < 0` at every positive steady state of the class,
  the positive steady state is unique.
* `rankOne_multistationary_iff`: when every positive steady state of the class is nondegenerate
  (`φ' ≠ 0`), the class has two distinct positive steady states iff one of them has `φ' > 0`.

The general-dimensional theorem needs the Brouwer degree, which the library has only for regular
values (`CRNT.regularDegree`, with homotopy invariance taking its analytic input as a hypothesis).
-/

namespace CRNT

namespace Network

open Filter Topology Set

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The mass-action field along the line `x₀ + t • v`, in units of `v`, read at coordinate `i₀`:
`φ(t) = F(x₀ + t • v)_{i₀} / v_{i₀}`. When the stoichiometric subspace is `span {v}`,
`F(x₀ + t • v) = φ(t) • v`. -/
noncomputable def lineField (N : Network S) (κ : RateConstants N) (x₀ v : Concentration S)
    (i₀ : S) (t : ℝ) : ℝ :=
  N.massActionVectorField κ (x₀ + t • v) i₀ / v i₀

theorem lineField_differentiable (N : Network S) (κ : RateConstants N) (x₀ v : Concentration S)
    (i₀ : S) : Differentiable ℝ (N.lineField κ x₀ v i₀) := by
  have hF := N.massActionVectorField_differentiable κ
  have hline : Differentiable ℝ fun t : ℝ => x₀ + t • v :=
    (differentiable_const _).add (differentiable_id.smul_const v)
  have hcomp : Differentiable ℝ fun t : ℝ => N.massActionVectorField κ (x₀ + t • v) :=
    hF.comp hline
  exact (differentiable_pi.mp hcomp i₀).div_const _

theorem lineField_continuous (N : Network S) (κ : RateConstants N) (x₀ v : Concentration S)
    (i₀ : S) : Continuous (N.lineField κ x₀ v i₀) :=
  (N.lineField_differentiable κ x₀ v i₀).continuous

/-- For a rank-one network the field is a multiple of `v`. -/
theorem massActionVectorField_eq_lineField_smul (N : Network S) (κ : RateConstants N)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S}
    (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S) (t : ℝ) :
    N.massActionVectorField κ (x₀ + t • v) = N.lineField κ x₀ v i₀ t • v := by
  have hmem : N.massActionVectorField κ (x₀ + t • v) ∈ N.stoichSubspace := by
    have hsum : N.massActionVectorField κ (x₀ + t • v)
        = ∑ r : N.R, (N.massActionRate κ r (x₀ + t • v)) • (N.reactionVector r) := by
      funext s
      simp only [massActionVectorField_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
  rw [hspan, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hci : c = N.lineField κ x₀ v i₀ t := by
    rw [lineField, ← hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hi₀, mul_one]
  rw [← hc, hci]

/-- Steady states on the line are the zeros of `φ`. -/
theorem isMassActionSteadyState_line_iff (N : Network S) (κ : RateConstants N)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S}
    (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S) (t : ℝ) :
    N.IsMassActionSteadyState κ (x₀ + t • v) ↔ N.lineField κ x₀ v i₀ t = 0 := by
  constructor
  · intro h
    have := h i₀
    simp only [lineField]
    rw [show N.massActionVectorField κ (x₀ + t • v) i₀ = 0 from this, zero_div]
  · intro h s
    rw [N.massActionVectorField_eq_lineField_smul κ hspan hi₀ x₀ t, h, zero_smul]
    rfl

theorem stoichCompatible_line (N : Network S) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x₀ : Concentration S) (t : ℝ) :
    N.StoichCompatible x₀ (x₀ + t • v) := by
  show (x₀ + t • v - x₀) ∈ N.stoichSubspace
  rw [add_sub_cancel_left, hspan]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem exists_line_of_stoichCompatible (N : Network S) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {x₀ x : Concentration S}
    (h : N.StoichCompatible x₀ x) : ∃ t : ℝ, x = x₀ + t • v := by
  have : x - x₀ ∈ Submodule.span ℝ {v} := hspan ▸ h
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨t, by rw [ht]; abel⟩

section Endpoints

omit [DecidableEq S]

variable (x₀ v : Concentration S) (hP : (Finset.univ.filter fun s => 0 < v s).Nonempty)
  (hQ : (Finset.univ.filter fun s => v s < 0).Nonempty)

/-- Left end of the class segment: `t₋ = max_{v_s > 0} (-x₀_s / v_s)`. -/
noncomputable def lineLeft : ℝ :=
  (Finset.univ.filter fun s => 0 < v s).sup' hP fun s => -x₀ s / v s

/-- Right end of the class segment: `t₊ = min_{v_s < 0} (-x₀_s / v_s)`. -/
noncomputable def lineRight : ℝ :=
  (Finset.univ.filter fun s => v s < 0).inf' hQ fun s => -x₀ s / v s

variable {x₀ v}

theorem lineLeft_neg (hx : x₀.Positive) : lineLeft x₀ v hP < 0 := by
  rw [lineLeft, Finset.sup'_lt_iff]
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (hx s)) hs

theorem lineRight_pos (hx : x₀.Positive) : 0 < lineRight x₀ v hQ := by
  rw [lineRight, Finset.lt_inf'_iff]
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (hx s)) hs

/-- The positive part of the class is the open segment `(t₋, t₊)`. -/
theorem line_positive_iff (hx : x₀.Positive) (t : ℝ) :
    (x₀ + t • v).Positive ↔ lineLeft x₀ v hP < t ∧ t < lineRight x₀ v hQ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [lineLeft, Finset.sup'_lt_iff]
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have := h s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [div_lt_iff₀ hs]; linarith
    · rw [lineRight, Finset.lt_inf'_iff]
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have := h s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [lt_div_iff_of_neg hs]; linarith
  · rintro ⟨hl, hr⟩ s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_trichotomy (v s) 0 with hs | hs | hs
    · have hle : lineRight x₀ v hQ ≤ -x₀ s / v s :=
        Finset.inf'_le _ (by simp [hs])
      have : t < -x₀ s / v s := lt_of_lt_of_le hr hle
      rw [lt_div_iff_of_neg hs] at this; linarith
    · rw [hs, mul_zero, add_zero]; exact hx s
    · have hle : -x₀ s / v s ≤ lineLeft x₀ v hP :=
        Finset.le_sup' (fun s => -x₀ s / v s) (by simp [hs])
      have : -x₀ s / v s < t := lt_of_le_of_lt hle hl
      rw [div_lt_iff₀ hs] at this; linarith

theorem line_nonneg_left (hx : x₀.Positive) : (x₀ + lineLeft x₀ v hP • v).Nonnegative := by
  intro s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases lt_trichotomy (v s) 0 with hs | hs | hs
  · nlinarith [lineLeft_neg hP hx, hx s]
  · rw [hs, mul_zero, add_zero]; exact (hx s).le
  · have hle : -x₀ s / v s ≤ lineLeft x₀ v hP :=
      Finset.le_sup' (fun s => -x₀ s / v s) (by simp [hs])
    rw [div_le_iff₀ hs] at hle; linarith

theorem line_nonneg_right (hx : x₀.Positive) : (x₀ + lineRight x₀ v hQ • v).Nonnegative := by
  intro s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases lt_trichotomy (v s) 0 with hs | hs | hs
  · have hle : lineRight x₀ v hQ ≤ -x₀ s / v s := Finset.inf'_le _ (by simp [hs])
    rw [le_div_iff_of_neg hs] at hle; linarith
  · rw [hs, mul_zero, add_zero]; exact (hx s).le
  · nlinarith [lineRight_pos hQ hx, hx s]

theorem exists_zero_coord_left :
    ∃ s, 0 < v s ∧ (x₀ + lineLeft x₀ v hP • v) s = 0 := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup' hP fun s => -x₀ s / v s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  refine ⟨s, hs, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lineLeft, heq]
  field_simp [hs.ne']
  ring

theorem exists_zero_coord_right :
    ∃ s, v s < 0 ∧ (x₀ + lineRight x₀ v hQ • v) s = 0 := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf' hQ fun s => -x₀ s / v s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  refine ⟨s, hs, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lineRight, heq]
  field_simp [hs.ne]
  ring

end Endpoints

section RankOne

variable (N : Network S) (κ : RateConstants N) {x₀ v : Concentration S}
  (hspan : N.stoichSubspace = Submodule.span ℝ {v})
  (hP : (Finset.univ.filter fun s => 0 < v s).Nonempty)
  (hQ : (Finset.univ.filter fun s => v s < 0).Nonempty)
  (hx : x₀.Positive)
  (hbd : ∀ x, N.StoichCompatible x₀ x → x.Nonnegative → ¬ x.Positive →
    ¬ N.IsMassActionSteadyState κ x)
  {i₀ : S} (hi₀ : v i₀ ≠ 0)

include hspan hx hbd hi₀

/-- At the left end of the class, `φ > 0`: the field points into the class. -/
theorem rankOne_lineField_left_pos : 0 < N.lineField κ x₀ v i₀ (lineLeft x₀ v hP) := by
  obtain ⟨s, hs, hz⟩ := exists_zero_coord_left hP (x₀ := x₀)
  have hnn := line_nonneg_left hP hx
  have hF := N.massActionVectorField_nonneg_of_zero κ hnn hz
  rw [N.massActionVectorField_eq_lineField_smul κ hspan hi₀, Pi.smul_apply, smul_eq_mul] at hF
  have hge : 0 ≤ N.lineField κ x₀ v i₀ (lineLeft x₀ v hP) := nonneg_of_mul_nonneg_left hF hs
  refine lt_of_le_of_ne hge (fun h0 => ?_)
  apply hbd _ (N.stoichCompatible_line hspan x₀ _) hnn (fun hp => (hp s).ne' hz)
  exact (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ _).mpr h0.symm

/-- At the right end of the class, `φ < 0`. -/
theorem rankOne_lineField_right_neg : N.lineField κ x₀ v i₀ (lineRight x₀ v hQ) < 0 := by
  obtain ⟨s, hs, hz⟩ := exists_zero_coord_right hQ (x₀ := x₀)
  have hnn := line_nonneg_right hQ hx
  have hF := N.massActionVectorField_nonneg_of_zero κ hnn hz
  rw [N.massActionVectorField_eq_lineField_smul κ hspan hi₀, Pi.smul_apply, smul_eq_mul] at hF
  have hle : N.lineField κ x₀ v i₀ (lineRight x₀ v hQ) ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  refine lt_of_le_of_ne hle (fun h0 => ?_)
  apply hbd _ (N.stoichCompatible_line hspan x₀ _) hnn (fun hp => (hp s).ne' hz)
  exact (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ _).mpr h0

/-- **Existence.** A rank-one network with compact classes and no boundary steady state in the
class of a positive `x₀` has a positive steady state in that class. -/
theorem rankOne_exists_positive_steadyState :
    ∃ t, lineLeft x₀ v hP < t ∧ t < lineRight x₀ v hQ ∧ N.lineField κ x₀ v i₀ t = 0 := by
  have hl := N.rankOne_lineField_left_pos κ hspan hP hx hbd hi₀
  have hr := N.rankOne_lineField_right_neg κ hspan hQ hx hbd hi₀
  have hab : lineLeft x₀ v hP ≤ lineRight x₀ v hQ :=
    ((lineLeft_neg hP hx).trans (lineRight_pos hQ hx)).le
  obtain ⟨t, ⟨ht1, ht2⟩, hz⟩ := intermediate_value_Icc' hab
    (N.lineField_continuous κ x₀ v i₀).continuousOn ⟨hr.le, hl.le⟩
  refine ⟨t, lt_of_le_of_ne ht1 ?_, lt_of_le_of_ne ht2 ?_, hz⟩
  · rintro rfl; exact hl.ne' hz
  · rintro rfl; exact hr.ne hz

/-- **Several steady states from the "wrong" sign.** If a positive steady state `x₀ + t • v` of the
class has `φ'(t) > 0`, there are positive steady states `x₀ + t₁ • v`, `x₀ + t₂ • v` with
`t₁ < t < t₂`: at least three in the class. -/
theorem rankOne_three_steadyStates_of_deriv_pos {t : ℝ}
    (ht : lineLeft x₀ v hP < t ∧ t < lineRight x₀ v hQ) (hz : N.lineField κ x₀ v i₀ t = 0)
    (hd : 0 < deriv (N.lineField κ x₀ v i₀) t) :
    ∃ t₁ t₂, lineLeft x₀ v hP < t₁ ∧ t₁ < t ∧ t < t₂ ∧ t₂ < lineRight x₀ v hQ ∧
      N.lineField κ x₀ v i₀ t₁ = 0 ∧ N.lineField κ x₀ v i₀ t₂ = 0 := by
  set φ := N.lineField κ x₀ v i₀ with hφ
  have hl := N.rankOne_lineField_left_pos κ hspan hP hx hbd hi₀
  have hr := N.rankOne_lineField_right_neg κ hspan hQ hx hbd hi₀
  have hcont := N.lineField_continuous κ x₀ v i₀
  have hder : HasDerivAt φ (deriv φ t) t :=
    ((N.lineField_differentiable κ x₀ v i₀) t).hasDerivAt
  have hslope : ∀ᶠ s in 𝓝[≠] t, 0 < φ s / (s - t) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hder).eventually (lt_mem_nhds hd)
    filter_upwards [this] with s hs
    rwa [slope_def_field, hz, sub_zero] at hs
  -- a negative value just left of `t`
  obtain ⟨s₁, hs₁, hs₁'⟩ : ∃ s₁, s₁ ∈ Ioo (lineLeft x₀ v hP) t ∧ φ s₁ < 0 := by
    have h1 : ∀ᶠ s in 𝓝[<] t, 0 < φ s / (s - t) := hslope.filter_mono (nhdsLT_le_nhdsNE t)
    have h2 : Ioo (lineLeft x₀ v hP) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht.1
    obtain ⟨s, hsl, hs⟩ := (h1.and h2).exists
    refine ⟨s, hs, ?_⟩
    have : s - t < 0 := by linarith [hs.2]
    by_contra hc
    push Not at hc
    have : φ s / (s - t) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc this.le
    linarith
  -- a positive value just right of `t`
  obtain ⟨s₂, hs₂, hs₂'⟩ : ∃ s₂, s₂ ∈ Ioo t (lineRight x₀ v hQ) ∧ 0 < φ s₂ := by
    have h1 : ∀ᶠ s in 𝓝[>] t, 0 < φ s / (s - t) := hslope.filter_mono (nhdsGT_le_nhdsNE t)
    have h2 : Ioo t (lineRight x₀ v hQ) ∈ 𝓝[>] t := Ioo_mem_nhdsGT ht.2
    obtain ⟨s, hsl, hs⟩ := (h1.and h2).exists
    refine ⟨s, hs, ?_⟩
    have : 0 < s - t := by linarith [hs.1]
    by_contra hc
    push Not at hc
    have : φ s / (s - t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc this.le
    linarith
  obtain ⟨t₁, ⟨h₁a, h₁b⟩, hz₁⟩ := intermediate_value_Icc' hs₁.1.le hcont.continuousOn
    ⟨hs₁'.le, hl.le⟩
  obtain ⟨t₂, ⟨h₂a, h₂b⟩, hz₂⟩ := intermediate_value_Icc' hs₂.2.le hcont.continuousOn
    ⟨hr.le, hs₂'.le⟩
  refine ⟨t₁, t₂, lt_of_le_of_ne h₁a ?_, lt_of_le_of_lt h₁b hs₁.2, lt_of_lt_of_le hs₂.1 h₂a,
    lt_of_le_of_ne h₂b ?_, hz₁, hz₂⟩
  · rintro rfl; exact hl.ne' hz₁
  · rintro rfl; exact hr.ne hz₂

/-- **Uniqueness from the "right" sign.** If `φ' < 0` at every positive steady state of the class,
the class has exactly one positive steady state. -/
theorem rankOne_existsUnique_of_deriv_neg
    (hneg : ∀ t, lineLeft x₀ v hP < t → t < lineRight x₀ v hQ → N.lineField κ x₀ v i₀ t = 0 →
      deriv (N.lineField κ x₀ v i₀) t < 0) :
    ∃! x, N.StoichCompatible x₀ x ∧ x.Positive ∧ N.IsMassActionSteadyState κ x := by
  obtain ⟨t, htl, htr, hz⟩ := N.rankOne_exists_positive_steadyState κ hspan hP hQ hx hbd hi₀
  refine ⟨x₀ + t • v, ⟨N.stoichCompatible_line hspan x₀ t, (line_positive_iff hP hQ hx t).mpr
    ⟨htl, htr⟩, (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t).mpr hz⟩, ?_⟩
  rintro y ⟨hyc, hyp, hys⟩
  obtain ⟨t', rfl⟩ := N.exists_line_of_stoichCompatible hspan hyc
  obtain ⟨htl', htr'⟩ := (line_positive_iff hP hQ hx t').mp hyp
  have hz' := (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t').mp hys
  have hI : (Ioo (lineLeft x₀ v hP) (lineRight x₀ v hQ)).OrdConnected := ordConnected_Ioo
  have hd : ∀ w ∈ Ioo (lineLeft x₀ v hP) (lineRight x₀ v hQ),
      HasDerivAt (N.lineField κ x₀ v i₀) (deriv (N.lineField κ x₀ v i₀) w) w :=
    fun w _ => ((N.lineField_differentiable κ x₀ v i₀) w).hasDerivAt
  have hn : ∀ w ∈ Ioo (lineLeft x₀ v hP) (lineRight x₀ v hQ), N.lineField κ x₀ v i₀ w = 0 →
      deriv (N.lineField κ x₀ v i₀) w < 0 := fun w hw hzw => hneg w hw.1 hw.2 hzw
  rcases lt_trichotomy t' t with hlt | heq | hgt
  · exact (no_two_zeros_of_deriv_neg hI hd hn ⟨htl', htr'⟩ ⟨htl, htr⟩ hz' hz hlt).elim
  · rw [heq]
  · exact (no_two_zeros_of_deriv_neg hI hd hn ⟨htl, htr⟩ ⟨htl', htr'⟩ hz hz' hgt).elim

/-- **Parameter region, rank one.** If every positive steady state of the class is nondegenerate
(`φ' ≠ 0`), the class contains two distinct positive steady states iff some positive steady state
of the class has `φ' > 0`. -/
theorem rankOne_multistationary_iff
    (hnd : ∀ t, lineLeft x₀ v hP < t → t < lineRight x₀ v hQ → N.lineField κ x₀ v i₀ t = 0 →
      deriv (N.lineField κ x₀ v i₀) t ≠ 0) :
    (∃ x y, x ≠ y ∧ N.StoichCompatible x₀ x ∧ x.Positive ∧ N.IsMassActionSteadyState κ x ∧
        N.StoichCompatible x₀ y ∧ y.Positive ∧ N.IsMassActionSteadyState κ y) ↔
      ∃ t, lineLeft x₀ v hP < t ∧ t < lineRight x₀ v hQ ∧ N.lineField κ x₀ v i₀ t = 0 ∧
        0 < deriv (N.lineField κ x₀ v i₀) t := by
  constructor
  · rintro ⟨x, y, hxy, hxc, hxp, hxs, hyc, hyp, hys⟩
    by_contra hno
    push Not at hno
    have hneg : ∀ t, lineLeft x₀ v hP < t → t < lineRight x₀ v hQ →
        N.lineField κ x₀ v i₀ t = 0 → deriv (N.lineField κ x₀ v i₀) t < 0 :=
      fun t h1 h2 h3 => lt_of_le_of_ne (hno t h1 h2 h3) (hnd t h1 h2 h3)
    obtain ⟨z, _, hzu⟩ := N.rankOne_existsUnique_of_deriv_neg κ hspan hP hQ hx hbd hi₀ hneg
    exact hxy ((hzu x ⟨hxc, hxp, hxs⟩).trans (hzu y ⟨hyc, hyp, hys⟩).symm)
  · rintro ⟨t, htl, htr, hz, hd⟩
    obtain ⟨t₁, t₂, h1, h2, _, _, hz₁, _⟩ :=
      N.rankOne_three_steadyStates_of_deriv_pos κ hspan hP hQ hx hbd hi₀ ⟨htl, htr⟩ hz hd
    refine ⟨x₀ + t₁ • v, x₀ + t • v, ?_, N.stoichCompatible_line hspan x₀ t₁,
      (line_positive_iff hP hQ hx t₁).mpr ⟨h1, h2.trans htr⟩,
      (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t₁).mpr hz₁,
      N.stoichCompatible_line hspan x₀ t, (line_positive_iff hP hQ hx t).mpr ⟨htl, htr⟩,
      (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t).mpr hz⟩
    intro heq
    have := congrFun heq i₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
    exact h2.ne (mul_right_cancel₀ hi₀ this)

end RankOne

end Network

end CRNT
