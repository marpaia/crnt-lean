import CRNT.Multistationarity.Toric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Constructing toric multistationarity from a shared sign vector

The converse to the Müller--Regensburger sign uniqueness criterion is elementary at the
abstract toric-set level.  Given nonzero `u ∈ S` and `v ∈ T` with the same coordinatewise
sign, set

`y_i = u_i / (exp(v_i)-1)`  when `v_i ≠ 0`, and `y_i = 1` otherwise,
`x_i = exp(v_i) y_i`.

Then `x,y > 0`, `x-y=u`, and `log x-log y=v`.  Thus a nonzero shared sign vector produces
two distinct positive toric states in a common compatibility class.
-/

namespace CRNT

variable {ι : Type*} [Fintype ι]

/-- The lower point in the sign-construction pair. -/
noncomputable def signConstructY (u v : ι → ℝ) : ι → ℝ :=
  fun i => if h : v i = 0 then 1 else u i / (Real.exp (v i) - 1)

/-- The upper point in the sign-construction pair. -/
noncomputable def signConstructX (u v : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (v i) * signConstructY u v i

/-- Same sign forces simultaneous vanishing. -/
theorem sameSign_eq_zero_iff {u v : ι → ℝ} (h : SameSign u v) (i : ι) :
    u i = 0 ↔ v i = 0 := by
  constructor
  · intro hu
    by_contra hv
    rcases lt_or_gt_of_ne hv with hvneg | hvpos
    · have := (h i).2.mpr hvneg
      simpa [hu] using this
    · have := (h i).1.mpr hvpos
      simpa [hu] using this
  · intro hv
    by_contra hu
    rcases lt_or_gt_of_ne hu with huneg | hupos
    · have := (h i).2.mp huneg
      simpa [hv] using this
    · have := (h i).1.mp hupos
      simpa [hv] using this

/-- The denominator `exp(v)-1` has the sign of `v`. -/
theorem exp_sub_one_same_sign (a : ℝ) :
    (0 < Real.exp a - 1 ↔ 0 < a) ∧ (Real.exp a - 1 < 0 ↔ a < 0) := by
  constructor
  · simpa [sub_pos] using Real.exp_lt_exp.trans' (show Real.exp 0 = 1 by simp)
  · simpa [sub_neg] using Real.exp_lt_exp

/-- The lower constructed point is positive coordinatewise. -/
theorem signConstructY_pos {u v : ι → ℝ} (h : SameSign u v) :
    ∀ i, 0 < signConstructY u v i := by
  intro i
  unfold signConstructY
  split_ifs with hv
  · exact one_pos
  · rcases lt_or_gt_of_ne hv with hvneg | hvpos
    · have huneg : u i < 0 := (h i).2.mpr hvneg
      have hden : Real.exp (v i) - 1 < 0 := (exp_sub_one_same_sign (v i)).2.mpr hvneg
      exact div_pos_of_neg_of_neg huneg hden
    · have hupos : 0 < u i := (h i).1.mpr hvpos
      have hden : 0 < Real.exp (v i) - 1 := (exp_sub_one_same_sign (v i)).1.mpr hvpos
      exact div_pos hupos hden

/-- The upper constructed point is positive coordinatewise. -/
theorem signConstructX_pos {u v : ι → ℝ} (h : SameSign u v) :
    ∀ i, 0 < signConstructX u v i := by
  intro i
  exact mul_pos (Real.exp_pos _) (signConstructY_pos h i)

/-- Exact displacement identity of the construction. -/
theorem signConstructX_sub_Y {u v : ι → ℝ} (h : SameSign u v) :
    signConstructX u v - signConstructY u v = u := by
  funext i
  simp only [Pi.sub_apply, signConstructX, signConstructY]
  split_ifs with hv
  · have hu : u i = 0 := (sameSign_eq_zero_iff h i).2 hv
    simp [hv, hu]
  · have hden : Real.exp (v i) - 1 ≠ 0 := by
      intro hz
      have hexp : Real.exp (v i) = 1 := sub_eq_zero.mp hz
      have : v i = 0 := by
        simpa using (Real.exp_injective (by simpa using hexp))
      exact hv this
    field_simp

/-- Exact log-ratio identity of the construction. -/
theorem log_signConstructX_sub_logY {u v : ι → ℝ} (h : SameSign u v) :
    (fun i => Real.log (signConstructX u v i) - Real.log (signConstructY u v i)) = v := by
  funext i
  have hy : 0 < signConstructY u v i := signConstructY_pos h i
  unfold signConstructX
  rw [Real.log_mul (Real.exp_ne_zero _) hy.ne', Real.log_exp]
  exact add_sub_cancel_right _ _

/-- A nonzero same-sign pair constructs two distinct positive points with prescribed
linear displacement and prescribed log displacement. -/
theorem exists_positive_pair_of_sameSign {u v : ι → ℝ}
    (h : SameSign u v) (hu : u ≠ 0) :
    ∃ x y : ι → ℝ,
      (∀ i, 0 < x i) ∧ (∀ i, 0 < y i) ∧ x ≠ y ∧
      x - y = u ∧
      (fun i => Real.log (x i) - Real.log (y i)) = v := by
  refine ⟨signConstructX u v, signConstructY u v,
    signConstructX_pos h, signConstructY_pos h, ?_, signConstructX_sub_Y h,
    log_signConstructX_sub_logY h⟩
  intro hxy
  apply hu
  rw [← signConstructX_sub_Y h, hxy, sub_self]

/-- **Sign incompatibility produces toric multistationarity.** -/
theorem exists_toric_multistationarity_of_signIncompatible
    (S T : Submodule ℝ (ι → ℝ)) (hbad : SignIncompatible S (orthSum T)) :
    ∃ xstar c x y : ι → ℝ,
      (∀ i, 0 < xstar i) ∧ (∀ i, 0 < c i) ∧
      x ∈ ToricSteadyStates S T xstar c ∧
      y ∈ ToricSteadyStates S T xstar c ∧ x ≠ y := by
  obtain ⟨u, huS, v, hvT, hsame, hu0⟩ := hbad
  obtain ⟨x, y, hx, hy, hxy, hdisp, hlog⟩ := exists_positive_pair_of_sameSign hsame hu0
  -- Choose the reference point `xstar = y` and the class representative `c = y`.
  refine ⟨y, y, x, y, hy, hy, ?_, ?_, hxy⟩
  · refine ⟨hx, ?_, ?_⟩
    · simpa [hdisp] using huS
    · simpa [hlog] using hvT
  · refine ⟨hy, ?_, ?_⟩
    · simp
    · simp [orthSum]

/-- **Full abstract toric criterion.** Sign compatibility is equivalent to uniqueness in
every positive toric compatibility class. -/
theorem signCompatible_iff_toric_subsingleton_all
    (S T : Submodule ℝ (ι → ℝ)) :
    SignCompatible S (orthSum T) ↔
      ∀ xstar c : ι → ℝ,
        (∀ i, 0 < xstar i) → (∀ i, 0 < c i) →
        (ToricSteadyStates S T xstar c).Subsingleton := by
  constructor
  · intro hsc xstar c _ _ x hx y hy
    exact toric_subsingleton_of_signCompatible hsc hx hy
  · intro hall
    rw [signCompatible_iff_not_signIncompatible]
    intro hbad
    obtain ⟨xstar, c, x, y, hxs, hc, hx, hy, hxy⟩ :=
      exists_toric_multistationarity_of_signIncompatible S T hbad
    exact hxy (hall xstar c hxs hc hx hy)

/-- Failure of sign compatibility is equivalent to the existence of a positive toric class
containing two distinct points. -/
theorem signIncompatible_iff_exists_toric_multistationarity
    (S T : Submodule ℝ (ι → ℝ)) :
    SignIncompatible S (orthSum T) ↔
      ∃ xstar c x y : ι → ℝ,
        (∀ i, 0 < xstar i) ∧ (∀ i, 0 < c i) ∧
        x ∈ ToricSteadyStates S T xstar c ∧
        y ∈ ToricSteadyStates S T xstar c ∧ x ≠ y := by
  constructor
  · exact exists_toric_multistationarity_of_signIncompatible S T
  · rintro ⟨xstar, c, x, y, hxs, hc, hx, hy, hxy⟩
    -- the goal is `SignIncompatible …`, not its negation, so argue by contradiction and
    -- convert through the iff rather than rewriting with it
    by_contra hni
    have hsc := (signCompatible_iff_not_signIncompatible S (orthSum T)).mpr hni
    exact hxy (toric_subsingleton_of_signCompatible hsc hx hy)

end CRNT
