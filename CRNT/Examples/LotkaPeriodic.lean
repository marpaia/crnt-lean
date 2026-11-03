import CRNT.Examples.LotkaFirstIntegral
import CRNT.Multistationarity.InheritanceAddReactions
import CRNT.Dynamics.FlowConstruction
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Lotka network has positive periodic orbits

Discharges step 4 of `CRNT/Examples/Lotka.lean` (`HasPositivePeriodicOrbitTarget`): for every
choice of positive rate constants the Lotka mass-action system has a nonconstant positive
periodic solution. Consequently the network has `OscillatoryCapacity`.

## Proof outline

1. *Global solution.* The vector field is clamped outside a box containing the compact
   sublevel set of the first integral `V`; the clamped field is globally Lipschitz and bounded,
   so it has a global solution. The level set `{V = h}` is closed and, near it, the clamped field
   equals the true field, along which `V` is locally constant; so the set of times spent on the
   level set is clopen, hence everything. The solution is therefore a genuine solution confined to
   the level set.
2. *Rotation.* With `(u, v) = (x - x*, y - y*)` one has `u' = -k x v`, `v' = k y u`, so the angular
   velocity `(u v' - v u')/(u² + v²) = k (y u² + x v²)/(u² + v²)` is at least `k δ > 0` on the
   level set. A continuous angle `Θ` with `(u, v) = Q (cos Θ, sin Θ)`, `Q > 0`, is obtained by
   integrating the angular velocity and checking that the defect `u sin Θ - v cos Θ` solves a
   scalar linear ODE with zero initial value.
3. *Return.* `Θ` reaches `Θ(0) + 2π` at some `T > 0`; then the point is on the same ray from the
   equilibrium and on the same level set, and `V` is strictly increasing along rays, so it is the
   starting point. Uniqueness for the clamped field makes the solution `T`-periodic.
-/

namespace CRNT
namespace Examples
namespace Lotka

open Filter Topology Set
open scoped NNReal

/-! ## Box bounds for sublevel sets -/

/-- Every sublevel set of the first integral lies in a box `[δ, M]²` with `δ > 0`. -/
theorem sublevel_box (κ : Network.RateConstants N) (h0 : 0 < κ.k grow) (h1 : 0 < κ.k prey)
    (h2 : 0 < κ.k decay) (c : ℝ) :
    ∃ δ M : ℝ, 0 < δ ∧ ∀ x : Concentration Species, x.Positive → firstIntegral κ x ≤ c →
      ∀ s, δ ≤ x s ∧ x s ≤ M := by
  set k := κ.k prey
  set a := κ.k decay
  set b := κ.k grow
  set mA := a - a * Real.log (2 * a / k)
  set mB := b - b * Real.log (2 * b / k)
  set CA := c - mB
  set CB := c - mA
  refine ⟨min (Real.exp (-CA / a)) (Real.exp (-CB / b)),
    max (2 * (CA - mA) / k) (2 * (CB - mB) / k), lt_min (Real.exp_pos _) (Real.exp_pos _), ?_⟩
  intro x hx hV s
  have hxA := hx A
  have hxB := hx B
  rw [firstIntegral_eq] at hV
  change k * x A - a * Real.log (x A) + (k * x B - b * Real.log (x B)) ≤ c at hV
  have lA := linLog_lower (k := k) (a := a) h1 h2 hxA
  have lB := linLog_lower (k := k) (a := b) h1 h0 hxB
  have hkA : 0 < k * x A := mul_pos h1 hxA
  have hkB : 0 < k * x B := mul_pos h1 hxB
  have tA : k * x A - a * Real.log (x A) ≤ CA := by simp only [CA, mB]; linarith
  have tB : k * x B - b * Real.log (x B) ≤ CB := by simp only [CB, mA]; linarith
  have loA := linLog_ge_exp h1 h2 hxA tA
  have loB := linLog_ge_exp h1 h0 hxB tB
  have hiA : x A ≤ 2 * (CA - mA) / k := by rw [le_div_iff₀ h1]; simp only [mA] at *; linarith
  have hiB : x B ≤ 2 * (CB - mB) / k := by rw [le_div_iff₀ h1]; simp only [mB] at *; linarith
  fin_cases s
  · exact ⟨(min_le_left _ _).trans loA, hiA.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans loB, hiB.trans (le_max_right _ _)⟩

/-! ## The first integral along curves -/

/-- Pointwise chain rule: along a curve that is positive at `t` and solves the mass-action
equation at `t`, the first integral has zero derivative at `t`. -/
theorem hasDerivAt_firstIntegral_comp (κ : Network.RateConstants N) {γ : ℝ → Concentration Species}
    {t : ℝ} (hpos : (γ t).Positive)
    (hder : ∀ s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    HasDerivAt (fun τ => firstIntegral κ (γ τ)) 0 t := by
  have h1 := hder A
  have h2 := hder B
  have hlA := h1.log (hpos A).ne'
  have hlB := h2.log (hpos B).ne'
  have := ((((h1.const_mul (κ.k prey)).add (h2.const_mul (κ.k prey))).sub
    (hlA.const_mul (κ.k decay))).sub (hlB.const_mul (κ.k grow)))
  unfold firstIntegral
  convert this using 1
  have hc := conservation_identity κ hpos
  rw [Fin.sum_univ_two] at hc
  simp only [firstIntegralGrad, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have hA := (hpos A).ne'
  have hB := (hpos B).ne'
  field_simp at hc ⊢
  linarith

/-! ## The clamped field -/

/-- Componentwise clamp to `[lo, hi]`. -/
noncomputable def clamp (lo hi : ℝ) (hle : lo ≤ hi) (x : Concentration Species) :
    Concentration Species := fun s => (Set.projIcc lo hi hle (x s) : ℝ)

theorem clamp_lipschitz (lo hi : ℝ) (hle : lo ≤ hi) : LipschitzWith 1 (clamp lo hi hle) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro s
  calc dist (clamp lo hi hle x s) (clamp lo hi hle y s)
      = dist (Set.projIcc lo hi hle (x s)) (Set.projIcc lo hi hle (y s)) := rfl
    _ ≤ dist (x s) (y s) := by
        have := (LipschitzWith.projIcc hle).dist_le_mul (x s) (y s)
        simpa using this
    _ ≤ dist x y := dist_le_pi_dist x y s

theorem clamp_mem (lo hi : ℝ) (hle : lo ≤ hi) (x : Concentration Species) :
    clamp lo hi hle x ∈ Set.Icc (fun _ => lo) (fun _ => hi) :=
  ⟨fun s => (Set.projIcc lo hi hle (x s)).2.1, fun s => (Set.projIcc lo hi hle (x s)).2.2⟩

theorem clamp_eq_self (lo hi : ℝ) (hle : lo ≤ hi) {x : Concentration Species}
    (hx : x ∈ Set.Icc (fun _ => lo) (fun _ => hi)) : clamp lo hi hle x = x := by
  funext s
  simp [clamp, Set.projIcc_of_mem hle ⟨hx.1 s, hx.2 s⟩]

/-- The clamped mass-action field is globally Lipschitz and bounded. -/
theorem clampedField_lipschitz_bounded (κ : Network.RateConstants N) (lo hi : ℝ)
    (hle : lo ≤ hi) :
    ∃ K B : ℝ≥0, LipschitzWith K (fun x => N.massActionVectorField κ (clamp lo hi hle x)) ∧
      ∀ x, ‖N.massActionVectorField κ (clamp lo hi hle x)‖ ≤ B := by
  set box := Set.Icc (fun _ : Species => lo) (fun _ => hi)
  obtain ⟨K, hK⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn (s := box)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (fun _ : Species => lo)) (b := fun _ => hi)).exists_bound_of_continuousOn
    (N.contDiff_massActionVectorField κ).continuous.continuousOn
  refine ⟨K * 1, ⟨max C 0, le_max_right _ _⟩, ?_, fun x => ?_⟩
  · have := hK.comp (s := Set.univ) (clamp_lipschitz lo hi hle).lipschitzOnWith
      (fun x _ => clamp_mem lo hi hle x)
    simpa [Function.comp_def, lipschitzOnWith_univ] using this
  · exact (hC _ (clamp_mem lo hi hle x)).trans (le_max_left _ _)

theorem continuousOn_firstIntegral (κ : Network.RateConstants N) :
    ContinuousOn (firstIntegral κ) {x : Concentration Species | x.Positive} := by
  have hne : ∀ s, ∀ x ∈ {x : Concentration Species | x.Positive}, x s ≠ 0 :=
    fun s x hx => (hx s).ne'
  unfold firstIntegral
  exact ((((continuous_const.mul (continuous_apply A)).continuousOn).add
    ((continuous_const.mul (continuous_apply B)).continuousOn)).sub
    (continuousOn_const.mul ((continuous_apply A).continuousOn.log (hne A)))).sub
    (continuousOn_const.mul ((continuous_apply B).continuousOn.log (hne B)))

/-! ## A global solution confined to a level set -/

/-- **Global confined solution.** For every positive start `p₀` there is a global solution of
the Lotka mass-action system through `p₀` staying on the level set `{V = V p₀}` inside a box
`[δ, M]²`, together with a globally Lipschitz field `g` that it also solves (used for
uniqueness). -/
theorem exists_confined_solution (κ : Network.RateConstants N) (h0 : 0 < κ.k grow)
    (h1 : 0 < κ.k prey) (h2 : 0 < κ.k decay) {p₀ : Concentration Species} (hp₀ : p₀.Positive) :
    ∃ (γ : ℝ → Concentration Species) (g : Concentration Species → Concentration Species)
      (K : ℝ≥0) (δ : ℝ),
      γ 0 = p₀ ∧ LipschitzWith K g ∧ 0 < δ ∧
      (∀ t, HasDerivAt γ (g (γ t)) t) ∧
      (∀ t, g (γ t) = N.massActionVectorField κ (γ t)) ∧
      (∀ t, (γ t).Positive ∧ firstIntegral κ (γ t) = firstIntegral κ p₀) ∧
      (∀ t s, δ ≤ γ t s) := by
  set h := firstIntegral κ p₀
  obtain ⟨δ, M, hδ, hbox⟩ := sublevel_box κ h0 h1 h2 h
  have hδM : δ ≤ M := by
    have := hbox p₀ hp₀ le_rfl A; linarith [this.1, this.2]
  set lo := δ / 2
  set hi := M + 1
  have hle : lo ≤ hi := by simp only [lo, hi]; linarith
  obtain ⟨K, Bd, hK, hBd⟩ := clampedField_lipschitz_bounded κ lo hi hle
  set g := fun x => N.massActionVectorField κ (clamp lo hi hle x)
  obtain ⟨γ, hγ0, hγd⟩ := ODE.exists_isIntegralCurve hK hBd p₀
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγd t).continuousAt
  set U := {x : Concentration Species | ∀ s, lo < x s ∧ x s < hi}
  set L := {x : Concentration Species | x.Positive ∧ firstIntegral κ x = h}
  have hLU : L ⊆ U := by
    intro x hx s
    have := hbox x hx.1 hx.2.le s
    constructor
    · simp only [lo]; linarith [this.1]
    · simp only [hi]; linarith [this.2]
  have hUpos : ∀ x ∈ U, x.Positive := fun x hx s =>
    lt_trans (by simp only [lo]; linarith) (hx s).1
  have hgU : ∀ x ∈ U, g x = N.massActionVectorField κ x := fun x hx => by
    simp only [g]
    rw [clamp_eq_self lo hi hle ⟨fun s => (hx s).1.le, fun s => (hx s).2.le⟩]
  have hUopen : IsOpen U := by
    have : U = ⋂ s, ({x : Concentration Species | lo < x s} ∩ {x | x s < hi}) := by
      ext x; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun s =>
      (isOpen_lt continuous_const (continuous_apply s)).inter
        (isOpen_lt (continuous_apply s) continuous_const)
  -- the set of times on the level set is clopen
  set Aset := {t : ℝ | γ t ∈ L}
  have hLclosed : IsClosed L := by
    have hKc := levelSetCompact κ h0 h1 h2 h
    have hcont : ContinuousOn (firstIntegral κ)
        {x : Concentration Species | x.Positive ∧ firstIntegral κ x ≤ h} :=
      (continuousOn_firstIntegral κ).mono fun x hx => hx.1
    have := hcont.preimage_isClosed_of_isClosed hKc.isClosed (isClosed_singleton (x := h))
    convert this using 1
    ext x
    simp only [L, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨⟨hx.1, hx.2.le⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
  have hclosed : IsClosed Aset := hLclosed.preimage hγc
  have hopen : IsOpen Aset := by
    rw [Metric.isOpen_iff]
    intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hUopen.preimage hγc) t (hLU ht)
    refine ⟨ε, hε, fun u hu => ?_⟩
    have hderiv : ∀ v ∈ Metric.ball t ε,
        HasDerivAt (fun τ => firstIntegral κ (γ τ)) 0 v := by
      intro v hv
      have hvU : γ v ∈ U := hball hv
      refine hasDerivAt_firstIntegral_comp κ (hUpos _ hvU) fun s => ?_
      have := (hasDerivAt_pi.mp (hγd v)) s
      rwa [hgU _ hvU] at this
    have hconst := (Metric.isOpen_ball).is_const_of_deriv_eq_zero
      (convex_ball t ε).isPreconnected
      (fun v hv => (hderiv v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hderiv v hv).deriv) hu (Metric.mem_ball_self hε)
    exact ⟨hUpos _ (hball hu), hconst.trans ht.2⟩
  have huniv : Aset = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩
    ⟨0, by simp only [Aset, Set.mem_ofPred_eq, hγ0]; exact ⟨hp₀, rfl⟩⟩
  have hmem : ∀ t, γ t ∈ L := fun t => by
    have : t ∈ Aset := huniv ▸ Set.mem_univ t
    exact this
  refine ⟨γ, g, K, δ, hγ0, hK, hδ, hγd, fun t => hgU _ (hLU (hmem t)), fun t => hmem t,
    fun t s => (hbox _ (hmem t).1 (hmem t).2.le s).1⟩

/-! ## Rotation and return -/

/-- `t ↦ k t − a log t` is strictly increasing on `[a/k, ∞)`. -/
theorem linLog_strictMono {k a s t : ℝ} (hk : 0 < k) (ha : 0 < a) (hs : a / k ≤ s)
    (hst : s < t) : k * s - a * Real.log s < k * t - a * Real.log t := by
  have hs0 : 0 < s := lt_of_lt_of_le (div_pos ha hk) hs
  have ht0 : 0 < t := hs0.trans hst
  have hlog : Real.log (t / s) < t / s - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos ht0 hs0) (by
      intro h; rw [div_eq_one_iff_eq hs0.ne'] at h; linarith)
  rw [Real.log_div ht0.ne' hs0.ne'] at hlog
  have hks : a ≤ k * s := by rw [div_le_iff₀ hk] at hs; linarith
  have : a * (t / s - 1) ≤ k * (t - s) := by
    rw [div_sub_one hs0.ne', mul_div_assoc', div_le_iff₀ hs0]
    nlinarith
  nlinarith

/-- **The Lotka network has a positive periodic orbit** for every choice of positive rate
constants (step 4 of `CRNT/Examples/Lotka.lean`). -/
theorem hasPositivePeriodicOrbit : HasPositivePeriodicOrbitTarget := by
  intro κ h0 h1 h2
  set k := κ.k prey
  set a := κ.k decay
  set b := κ.k grow
  set xs := a / k
  set ys := b / k
  have hxs : 0 < xs := div_pos h2 h1
  have hys : 0 < ys := div_pos h0 h1
  -- start at `(2 x*, y*)`
  set p₀ : Concentration Species := ![2 * xs, ys]
  have hp₀ : p₀.Positive := by
    intro s; fin_cases s
    · show 0 < 2 * xs; positivity
    · exact hys
  have hp₀ne : p₀ ≠ equilibrium κ := by
    intro h
    have := congrFun h A
    simp only [p₀, equilibrium, Matrix.cons_val_zero] at this
    change 2 * xs = xs at this
    linarith
  obtain ⟨γ, g, K, δ, hγ0, hK, hδ, hγd, hgf, hlev, hlow⟩ :=
    exists_confined_solution κ h0 h1 h2 hp₀
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγd t).continuousAt
  -- coordinates relative to the equilibrium
  set u : ℝ → ℝ := fun t => γ t A - xs
  set v : ℝ → ℝ := fun t => γ t B - ys
  have hfA : ∀ t, N.massActionVectorField κ (γ t) A = -k * γ t A * v t := by
    intro t; rw [field_A]; simp only [v, ys]; field_simp; ring
  have hfB : ∀ t, N.massActionVectorField κ (γ t) B = k * γ t B * u t := by
    intro t; rw [field_B]; simp only [u, xs]; field_simp; ring
  have hu' : ∀ t, HasDerivAt u (-k * γ t A * v t) t := fun t => by
    have := (hasDerivAt_pi.mp (hγd t)) A
    rw [hgf, hfA] at this
    exact this.sub_const xs
  have hv' : ∀ t, HasDerivAt v (k * γ t B * u t) t := fun t => by
    have := (hasDerivAt_pi.mp (hγd t)) B
    rw [hgf, hfB] at this
    exact this.sub_const ys
  -- the orbit never meets the equilibrium
  have hVgt : firstIntegral κ (equilibrium κ) < firstIntegral κ p₀ :=
    firstIntegral_gt_equilibrium κ h0 h1 h2 hp₀ hp₀ne
  have hr : ∀ t, 0 < u t ^ 2 + v t ^ 2 := by
    intro t
    by_contra hle
    push Not at hle
    have hu0 : u t = 0 := by nlinarith [sq_nonneg (u t), sq_nonneg (v t)]
    have hv0 : v t = 0 := by nlinarith [sq_nonneg (u t), sq_nonneg (v t)]
    have heq : γ t = equilibrium κ := by
      funext s; fin_cases s
      · show γ t A = κ.k decay / κ.k prey; simp only [u] at hu0; linarith
      · show γ t B = κ.k grow / κ.k prey; simp only [v] at hv0; linarith
    have := (hlev t).2
    rw [heq] at this
    linarith
  -- angular velocity and radial rate
  set β : ℝ → ℝ := fun t => k * (γ t B * u t ^ 2 + γ t A * v t ^ 2) / (u t ^ 2 + v t ^ 2)
  set α : ℝ → ℝ := fun t => k * u t * v t * (γ t B - γ t A) / (u t ^ 2 + v t ^ 2)
  have hcA : Continuous fun t => γ t A := (continuous_apply A).comp hγc
  have hcB : Continuous fun t => γ t B := (continuous_apply B).comp hγc
  have hcu : Continuous u := hcA.sub continuous_const
  have hcv : Continuous v := hcB.sub continuous_const
  have hβc : Continuous β := by
    refine Continuous.div ?_ ((hcu.pow 2).add (hcv.pow 2)) fun t => (hr t).ne'
    exact continuous_const.mul ((hcB.mul (hcu.pow 2)).add (hcA.mul (hcv.pow 2)))
  have hαc : Continuous α := by
    refine Continuous.div ?_ ((hcu.pow 2).add (hcv.pow 2)) fun t => (hr t).ne'
    exact ((continuous_const.mul hcu).mul hcv).mul (hcB.sub hcA)
  set Θ : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, β τ
  set Aα : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, α τ
  have hΘ' : ∀ t, HasDerivAt Θ (β t) t := fun t => (hβc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hA' : ∀ t, HasDerivAt Aα (α t) t := fun t => (hαc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hΘ0 : Θ 0 = 0 := by simp [Θ]
  have hA0 : Aα 0 = 0 := by simp [Aα]
  -- defect `P = u sin Θ − v cos Θ` vanishes identically
  set P : ℝ → ℝ := fun t => u t * Real.sin (Θ t) - v t * Real.cos (Θ t)
  set Q : ℝ → ℝ := fun t => u t * Real.cos (Θ t) + v t * Real.sin (Θ t)
  have hP' : ∀ t, HasDerivAt (fun t => P t * Real.exp (-Aα t)) 0 t := by
    intro t
    have hs := (hΘ' t).sin
    have hc := (hΘ' t).cos
    have he := ((hA' t).neg).exp
    have := ((((hu' t).mul hs).sub ((hv' t).mul hc)).mul he)
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at this
    convert this using 1
    have hr0 := (hr t).ne'
    simp only [β, α] at *
    field_simp
    ring
  have hQ' : ∀ t, HasDerivAt (fun t => Q t * Real.exp (-Aα t)) 0 t := by
    intro t
    have hs := (hΘ' t).sin
    have hc := (hΘ' t).cos
    have he := ((hA' t).neg).exp
    have := ((((hu' t).mul hc).add ((hv' t).mul hs)).mul he)
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at this
    convert this using 1
    have hr0 := (hr t).ne'
    simp only [β, α] at *
    field_simp
    ring
  have hPconst : ∀ t, P t * Real.exp (-Aα t) = P 0 * Real.exp (-Aα 0) := fun t =>
    is_const_of_deriv_eq_zero (fun τ => (hP' τ).differentiableAt) (fun τ => (hP' τ).deriv) t 0
  have hQconst : ∀ t, Q t * Real.exp (-Aα t) = Q 0 * Real.exp (-Aα 0) := fun t =>
    is_const_of_deriv_eq_zero (fun τ => (hQ' τ).differentiableAt) (fun τ => (hQ' τ).deriv) t 0
  have hu0 : u 0 = xs := by
    simp only [u, hγ0, p₀, Matrix.cons_val_zero]; ring
  have hv0 : v 0 = 0 := by
    simp [v, hγ0, p₀]
  have hP0 : P 0 = 0 := by simp [P, hΘ0, hv0]
  have hQ0 : Q 0 = xs := by simp [Q, hΘ0, hu0, hv0]
  have hPz : ∀ t, P t = 0 := fun t => by
    have := hPconst t
    rw [hP0, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right (Real.exp_pos _).ne'
  have hQpos : ∀ t, 0 < Q t := fun t => by
    have := hQconst t
    rw [hQ0, hA0, neg_zero, Real.exp_zero, mul_one] at this
    by_contra hle
    push Not at hle
    have : Q t * Real.exp (-Aα t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
    linarith
  -- the angle grows at rate at least `k δ`
  have hβlow : ∀ t, k * δ ≤ β t := by
    intro t
    have hr0 := hr t
    simp only [β]
    rw [le_div_iff₀ hr0]
    have := hlow t A
    have := hlow t B
    nlinarith [sq_nonneg (u t), sq_nonneg (v t), mul_le_mul_of_nonneg_right (hlow t B)
      (sq_nonneg (u t)), mul_le_mul_of_nonneg_right (hlow t A) (sq_nonneg (v t))]
  have hkd : 0 < k * δ := mul_pos h1 hδ
  have hΘlow : ∀ t, 0 ≤ t → k * δ * t ≤ Θ t := by
    have hd : ∀ t, HasDerivAt (fun t => Θ t - k * δ * t) (β t - k * δ) t := fun t => by
      have := (hΘ' t).fun_sub ((hasDerivAt_id' t).const_mul (k * δ))
      rwa [mul_one] at this
    have hmono : Monotone (fun t => Θ t - k * δ * t) := by
      refine monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt) fun t => ?_
      rw [(hd t).deriv]; linarith [hβlow t]
    intro t ht
    have := hmono ht
    simp only [hΘ0, mul_zero, sub_zero] at this
    linarith
  -- a full turn at some positive time `T`
  set t₁ := 2 * Real.pi / (k * δ)
  have ht₁ : 0 ≤ t₁ := by positivity
  have hΘt₁ : 2 * Real.pi ≤ Θ t₁ := by
    have := hΘlow t₁ ht₁
    simp only [t₁] at this
    rwa [mul_div_cancel₀ _ hkd.ne'] at this
  obtain ⟨T, hTmem, hΘT⟩ := intermediate_value_Icc ht₁
    (fun t _ => (hΘ' t).continuousAt.continuousWithinAt)
    ⟨by rw [hΘ0]; positivity, hΘt₁⟩
  have hTpos : 0 < T := by
    rcases hTmem.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hΘ0] at hΘT; linarith [Real.pi_pos]
  -- return to the starting point
  have hvT : v T = 0 := by
    have := hPz T
    simp only [P, hΘT, Real.sin_two_pi, Real.cos_two_pi] at this
    linarith
  have huT : 0 < u T := by
    have := hQpos T
    simp only [Q, hΘT, Real.sin_two_pi, Real.cos_two_pi] at this
    linarith
  have hγT : γ T = p₀ := by
    have hV := (hlev T).2
    have hBT : γ T B = ys := by simp only [v] at hvT; linarith
    rw [firstIntegral_eq, firstIntegral_eq, hBT] at hV
    have hp0A : p₀ A = 2 * xs := rfl
    have hp0B : p₀ B = ys := rfl
    rw [hp0A, hp0B] at hV
    have hAT : γ T A = 2 * xs := by
      have hge : xs ≤ γ T A := by simp only [u] at huT; linarith
      rcases lt_trichotomy (γ T A) (2 * xs) with hlt | heq | hgt
      · have := linLog_strictMono h1 h2 hge hlt
        change k * γ T A - a * Real.log (γ T A) < k * (2 * xs) - a * Real.log (2 * xs) at this
        change k * γ T A - a * Real.log (γ T A) + _ = k * (2 * xs) - a * Real.log (2 * xs) + _
          at hV
        linarith
      · exact heq
      · have := linLog_strictMono h1 h2 (by linarith : xs ≤ 2 * xs) hgt
        change k * (2 * xs) - a * Real.log (2 * xs) < k * γ T A - a * Real.log (γ T A) at this
        change k * γ T A - a * Real.log (γ T A) + _ = k * (2 * xs) - a * Real.log (2 * xs) + _
          at hV
        linarith
    funext s; fin_cases s
    · exact hAT
    · exact hBT
  -- periodicity from uniqueness for the clamped field
  have hper : Function.Periodic γ T := by
    have hshift : ∀ t, HasDerivAt (fun τ => γ (τ + T)) (g (γ (t + T))) t := fun t => by
      have hg : HasDerivAt (fun τ : ℝ => τ + T) 1 t := by
        simpa using (hasDerivAt_id t).add_const T
      simpa [Function.comp_def] using (hγd (t + T)).scomp t hg
    have := ODE_solution_unique_univ (v := fun _ => g) (s := fun _ => Set.univ) (t₀ := 0)
      (fun _ => hK.lipschitzOnWith) (fun t => ⟨hshift t, Set.mem_univ _⟩)
      (fun t => ⟨hγd t, Set.mem_univ _⟩) (by simp only [zero_add]; rw [hγT, hγ0])
    exact fun t => congrFun this t
  -- the orbit is not constant
  have hnc : ∃ t, γ t ≠ γ 0 := by
    by_contra hcon
    push Not at hcon
    have hconst : γ = fun _ => γ 0 := funext hcon
    have h0d := hγd 0
    rw [hconst] at h0d
    have hz := h0d.unique (hasDerivAt_const 0 (γ 0))
    have hB := congrFun hz B
    rw [hgf 0] at hB
    simp only [Pi.zero_apply] at hB
    rw [hfB, hu0, hγ0] at hB
    have hpB : p₀ B = ys := rfl
    rw [hpB] at hB
    have : k * ys * xs ≠ 0 := by positivity
    exact this hB
  have hsol : ∀ t s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t := by
    intro t s
    have := (hasDerivAt_pi.mp (hγd t)) s
    rwa [hgf] at this
  have hposγ : ∀ t, (γ t).Positive := fun t => (hlev t).1
  exact ⟨⟨γ, T, hTpos, hposγ, hsol, hper, hnc⟩⟩

/-- **The Lotka network has oscillatory capacity.** -/
theorem oscillatoryCapacity : N.OscillatoryCapacity := by
  let κ : Network.RateConstants N := ⟨fun _ => 1, fun _ => one_pos⟩
  exact oscillatoryCapacity_of_target hasPositivePeriodicOrbit κ one_pos one_pos one_pos

end Lotka
end Examples
end CRNT
