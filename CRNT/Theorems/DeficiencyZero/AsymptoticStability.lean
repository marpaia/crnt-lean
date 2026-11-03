import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.Confinement
import CRNT.Theorems.DeficiencyZero.Stability
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Dynamics.LaSalle
import CRNT.Dynamics.FlowConstruction
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Local asymptotic stability of the complex-balanced equilibrium

The Horn–Jackson stability theorem: for a weakly reversible deficiency-zero network, the
complex-balanced equilibrium `x*` of a positive compatibility class is locally
asymptotically stable for the mass-action dynamics `ẋ = f(x)`.

The proof assembles the previously-established pieces. Because Mathlib's flow theory needs a
globally bounded Lipschitz field, the genuine field `f` is replaced by its
bounded-Lipschitz cutoff `f ∘ clampBox B` (`exists_cutoff`); `ODE.exists_flow` turns that
into a `Flow ℝ≥0`. On a sublevel set of the relative entropy contained in the interior of
the box the cutoff coincides with `f`, and:

* `exists_field_lower_bound`: `f_s(x) ≥ −L·x_s` on the box (each consuming reaction's monomial
  carries a factor `x_s`), giving the forward differential inequality;
* `orbit_pos`: the cutoff orbit stays strictly positive (first-crossing via
  `ge_mul_exp_of_forward_deriv_ge`);
* `orbit_relEntropy_le`: it stays in the initial relative-entropy sublevel set (first exit
  from the box contradicts Lyapunov descent + coercivity);
* `relEntropy_continuous` / `isCompact_relEntropy_sublevel` / `positive_of_relEntropy_lt`:
  the sublevel set is compact and — below every reference coordinate — contained in the open
  orthant (boundary repulsion), so it absorbs the orbit;
* `sub_mem_stoichSubspace_of_solution`: the orbit stays in `x₀`'s compatibility class.

`omegaLimit_eq_singleton_of_local` then runs `Flow.laSalle`: the relative entropy is constant
on the ω-limit set, so the dissipation vanishes there, forcing each ω-point to be
complex-balanced (`complexBalanced_of_dissipation_eq_zero`) in `x₀`'s positive class — hence
equal to `x*` by deficiency-zero uniqueness (`isComplexBalanced_unique_in_positiveClass`).
Thus `ω(x₀) = {x*}`.

-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT

/-- **Forward Grönwall lower bound.** If `z' ≥ −L·z` on `[0,T]` then
`z 0 · exp(−L·T) ≤ z T`. (Used for the first-crossing positivity of the orbit.) -/
theorem ge_mul_exp_of_forward_deriv_ge {z z' : ℝ → ℝ} {L T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt z (z' t) t)
    (hineq : ∀ t ∈ Set.Icc (0:ℝ) T, -(L * z t) ≤ z' t) :
    z 0 * Real.exp (-(L * T)) ≤ z T := by
  set w : ℝ → ℝ := fun t => z t * Real.exp (L * t) with hw
  have hwd : ∀ t ∈ Set.Icc (0:ℝ) T,
      HasDerivAt w ((z' t + L * z t) * Real.exp (L * t)) t := by
    intro t ht
    have he : HasDerivAt (fun s => Real.exp (L * s)) (Real.exp (L * t) * L) t := by
      simpa using (((hasDerivAt_id t).const_mul L)).exp
    have hm := (hd t ht).mul he
    have hval : z' t * Real.exp (L * t) + z t * (Real.exp (L * t) * L)
        = (z' t + L * z t) * Real.exp (L * t) := by ring
    rw [hw, ← hval]; exact hm
  have hcont : ContinuousOn w (Set.Icc 0 T) :=
    fun t ht => (hwd t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn w (Set.Icc 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcont ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact (hwd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hwd t (Set.Ioo_subset_Icc_self ht)).deriv]
      have := hineq t (Set.Ioo_subset_Icc_self ht)
      exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have h0T : w 0 ≤ w T := hmono ⟨le_refl 0, hT⟩ ⟨hT, le_refl T⟩ hT
  simp only [hw, mul_zero, Real.exp_zero, mul_one] at h0T
  have hpos : (0:ℝ) < Real.exp (L * T) := Real.exp_pos _
  calc z 0 * Real.exp (-(L * T)) = z 0 / Real.exp (L * T) := by rw [Real.exp_neg]; ring
    _ ≤ z T := by rw [div_le_iff₀ hpos]; linarith [h0T]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
/-- **Continuity of the relative entropy** in its second argument. Each coordinate term
`x_s ↦ x_s·log(x_s/x*_s)` extends continuously through `0` (via `t·log t`), so the finite
sum is continuous on all of `Concentration S`. -/
theorem relEntropy_continuous {xstar : Concentration S} (hxs : xstar.Positive) :
    Continuous (fun x : Concentration S => relEntropy xstar x) := by
  unfold relEntropy
  refine continuous_finsetSum _ fun s _ => ?_
  have hne : xstar s ≠ 0 := ne_of_gt (hxs s)
  have hterm : (fun x : Concentration S => x s * Real.log (x s / xstar s))
      = fun x : Concentration S => xstar s * ((x s / xstar s) * Real.log (x s / xstar s)) := by
    funext x
    have hcancel : xstar s * (x s / xstar s) = x s := by
      field_simp
    rw [← mul_assoc, hcancel]
  have hdiv : Continuous (fun x : Concentration S => x s / xstar s) := by
    simp only [div_eq_mul_inv]
    exact (continuous_apply s).mul continuous_const
  have hc1 : Continuous (fun x : Concentration S => x s * Real.log (x s / xstar s)) := by
    rw [hterm]
    exact continuous_const.mul (Real.continuous_mul_log.comp hdiv)
  exact (hc1.sub (continuous_apply s)).add continuous_const

omit [DecidableEq S] in
/-- A boundary point of the orthant has relative entropy at least the reference coordinate:
if `y` is nonnegative with `y s = 0` then `relEntropy x* y ≥ x*_s`. -/
theorem relEntropy_ge_of_coord_zero {xstar y : Concentration S} (hxs : xstar.Positive)
    (hy : y.Nonnegative) {s : S} (h0 : y s = 0) : xstar s ≤ relEntropy xstar y := by
  have hterm : ∀ i, 0 ≤ y i * Real.log (y i / xstar i) - y i + xstar i :=
    fun i => relEntropyTerm_nonneg (hy i) (hxs i)
  have hs : y s * Real.log (y s / xstar s) - y s + xstar s = xstar s := by
    rw [h0]; simp
  calc xstar s = y s * Real.log (y s / xstar s) - y s + xstar s := hs.symm
    _ ≤ relEntropy xstar y :=
        Finset.single_le_sum (f := fun i => y i * Real.log (y i / xstar i) - y i + xstar i)
          (fun i _ => hterm i) (Finset.mem_univ s)

omit [DecidableEq S] in
/-- **Boundary repulsion.** If the relative entropy is strictly below every reference
coordinate, then a nonnegative point is strictly positive. -/
theorem positive_of_relEntropy_lt {xstar y : Concentration S} (hxs : xstar.Positive)
    (hy : y.Nonnegative) {δ : ℝ} (hδ : ∀ s, δ ≤ xstar s) (h : relEntropy xstar y < δ) :
    y.Positive := by
  intro s
  rcases lt_or_eq_of_le (hy s) with hpos | hzero
  · exact hpos
  · exact absurd (le_trans (hδ s) (relEntropy_ge_of_coord_zero hxs hy hzero.symm)) (not_le.mpr h)

omit [DecidableEq S] in
/-- **Compactness of relative-entropy sublevel sets** on the nonnegative orthant. Coercivity
bounds each coordinate, so the set is closed and bounded, hence compact. -/
theorem isCompact_relEntropy_sublevel {xstar : Concentration S} (hxs : xstar.Positive)
    (C : ℝ) : IsCompact {y : Concentration S | y.Nonnegative ∧ relEntropy xstar y ≤ C} := by
  set box : Set (Concentration S) :=
    Set.univ.pi (fun s : S => Set.Icc (0:ℝ) (max (Real.exp 2 * xstar s) C)) with hbox
  have hboxcpt : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hnn : IsClosed {y : Concentration S | y.Nonnegative} := by
    have heq : {y : Concentration S | y.Nonnegative} = ⋂ s, {y : Concentration S | 0 ≤ y s} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_iInter]; rfl
    rw [heq]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  refine hboxcpt.of_isClosed_subset
    (hnn.inter (isClosed_le (relEntropy_continuous hxs) continuous_const)) ?_
  rintro y ⟨hynn, hyC⟩
  exact Set.mem_univ_pi.2 fun s => ⟨hynn s, relEntropy_coord_le hxs hynn hyC s⟩

/-- **Positivity of the confined orbit.** A solution of the cutoff dynamics
`Γ' = f(clampBox B Γ)` starting positive stays strictly positive on `[0, ∞)`. The field
obeys `f_s(x) ≥ −L·x_s` on the (nonnegative) box, so each coordinate satisfies the forward
differential inequality `Γ_s' ≥ −L·Γ_s` on any interval where the orbit is nonnegative; a
first-crossing argument (via `ge_mul_exp_of_forward_deriv_ge`) rules out reaching `0`. -/
theorem orbit_pos (N : Network S) (κ : N.RateConstants) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ x : Concentration S, x.Nonnegative → (∀ s, x s ≤ B) →
      ∀ s, -(L * x s) ≤ N.massActionVectorField κ x s)
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓd : ∀ t, HasDerivAt Γ (N.massActionVectorField κ (clampBox B (Γ t))) t) :
    ∀ t, 0 ≤ t → (Γ t).Positive := by
  have hdiff : Differentiable ℝ Γ := fun t => (hΓd t).differentiableAt
  have hcs : ∀ s, Continuous (fun t => Γ t s) := fun s => (continuous_apply s).comp hdiff.continuous
  intro T hT
  by_contra hcon
  have hcon' : ∃ s, Γ T s ≤ 0 := by
    by_contra h; simp only [not_exists, not_le] at h; exact hcon h
  obtain ⟨s₀, hs₀⟩ := hcon'
  set A : Set ℝ := {t | 0 ≤ t ∧ ∃ s, Γ t s ≤ 0} with hA
  have hAne : A.Nonempty := ⟨T, hT, s₀, hs₀⟩
  have hAcl : IsClosed A := by
    have heq : A = Set.Ici 0 ∩ ⋃ s, {t | Γ t s ≤ 0} := by
      ext t; simp only [hA, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iUnion]
    rw [heq]
    exact isClosed_Ici.inter
      (isClosed_iUnion_of_finite fun s => isClosed_le (hcs s) continuous_const)
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
  set t₁ := sInf A with ht₁def
  have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
  have ht₁0 : 0 ≤ t₁ := ht₁A.1
  obtain ⟨s₁, hs₁⟩ := ht₁A.2
  have hbefore : ∀ t, 0 ≤ t → t < t₁ → (Γ t).Positive := by
    intro t ht htlt s
    by_contra hle
    rw [not_lt] at hle
    exact absurd (csInf_le hAbdd ⟨ht, s, hle⟩) (not_le.mpr htlt)
  rcases eq_or_lt_of_le ht₁0 with ht₁eq | ht₁pos
  · rw [← ht₁eq] at hs₁
    exact absurd (hΓ0 s₁) (not_lt.mpr hs₁)
  · have key : ∀ t ∈ Set.Ico 0 t₁, Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁ := by
      intro t ht
      refine ge_mul_exp_of_forward_deriv_ge ht.1 (fun τ _ => (hasDerivAt_pi.mp (hΓd τ)) s₁) ?_
      intro τ hτ
      have hτlt : τ < t₁ := lt_of_le_of_lt hτ.2 ht.2
      have hnn : (Γ τ).Nonnegative := (hbefore τ hτ.1 hτlt).nonnegative
      have hclnn : ∀ s, 0 ≤ clampBox B (Γ τ) s := fun s => by
        simp only [clampBox]; exact le_max_of_le_right (le_min hB (hnn s))
      have hclle : ∀ s, clampBox B (Γ τ) s ≤ B := fun s => (clampBox_mem hB (Γ τ) s).2
      have hb := hbound (clampBox B (Γ τ)) hclnn hclle s₁
      have hclle₁ : clampBox B (Γ τ) s₁ ≤ Γ τ s₁ := by
        simp only [clampBox]; exact max_le (by linarith [hnn s₁]) (min_le_right B (Γ τ s₁))
      calc -(L * Γ τ s₁) ≤ -(L * clampBox B (Γ τ) s₁) := by
              linarith [mul_le_mul_of_nonneg_left hclle₁ hL]
        _ ≤ N.massActionVectorField κ (clampBox B (Γ τ)) s₁ := hb
    have hclosed : IsClosed {t : ℝ | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁} :=
      isClosed_le
        (continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)))
        (hcs s₁)
    have ht₁mem : t₁ ∈ {t : ℝ | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁} := by
      have hmemcl : t₁ ∈ closure (Set.Ico 0 t₁) := by
        rw [closure_Ico (ne_of_lt ht₁pos)]; exact ⟨ht₁0, le_refl t₁⟩
      exact hclosed.closure_subset_iff.mpr (fun t ht => key t ht) hmemcl
    exact absurd (lt_of_lt_of_le (mul_pos (hΓ0 s₁) (Real.exp_pos _)) ht₁mem) (not_lt.mpr hs₁)

/-- The mass-action vector field always lies in the stoichiometric subspace: it is a linear
combination of reaction vectors. -/
theorem massActionVectorField_mem_stoichSubspace (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.massActionVectorField κ x ∈ N.stoichSubspace := by
  have hsum : N.massActionVectorField κ x
      = ∑ r : N.R, (N.massActionRate κ r x) • (N.reactionVector r) := by
    funext s
    rw [massActionVectorField_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- **Displacement along a mass-action solution stays in the stoichiometric subspace.** If
`γ` solves `ẋ = f(x)` on `[a, b]`, then `γ b − γ a ∈ stoichSubspace`. -/
theorem sub_mem_stoichSubspace_of_solution (N : Network S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a ≤ b)
    (hsol : ∀ t ∈ Set.Icc a b, HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    γ b - γ a ∈ N.stoichSubspace := by
  rw [← orthSum_orthSum N.stoichSubspace, mem_orthSum]
  intro w hw
  have hp : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun τ => ∑ i, w i * γ τ i) (0 : ℝ) (Set.Icc a b) t := by
    intro t ht
    have hfun : (fun τ : ℝ => ∑ i, w i * γ τ i)
        = ∑ i ∈ (Finset.univ : Finset S), (fun τ : ℝ => w i * γ τ i) := by
      funext τ; rw [Finset.sum_apply]
    have hzero : (∑ i, w i * N.massActionVectorField κ (γ t) i) = 0 :=
      (mem_orthSum.mp hw) _ (massActionVectorField_mem_stoichSubspace N κ (γ t))
    rw [hfun]
    have hd := HasDerivAt.sum (u := (Finset.univ : Finset S))
      (fun i _ => HasDerivAt.const_mul (w i) ((hasDerivAt_pi.mp (hsol t ht)) i))
    rw [hzero] at hd
    exact hd.hasDerivWithinAt
  have hconst : (∑ i, w i * γ b i) = (∑ i, w i * γ a i) := by
    have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hp
      (fun t _ => by simp) (convex_Icc a b) ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩
    simp only [zero_mul] at hle
    have h0 : ‖(∑ i, w i * γ b i) - (∑ i, w i * γ a i)‖ = 0 := le_antisymm hle (norm_nonneg _)
    rwa [norm_eq_zero, sub_eq_zero] at h0
  calc ∑ i, (γ b - γ a) i * w i
      = ∑ i, (w i * γ b i - w i * γ a i) :=
        Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]; ring
    _ = (∑ i, w i * γ b i) - (∑ i, w i * γ a i) :=
        Finset.sum_sub_distrib (f := fun i => w i * γ b i) (g := fun i => w i * γ a i)
    _ = 0 := by rw [hconst, sub_self]

omit [DecidableEq S] in
/-- On a relative-entropy sublevel set inside the interior of the box, the clamp is the
identity. -/
theorem clampBox_eq_of_sublevel {xstar z : Concentration S} {C B : ℝ} (hxs : xstar.Positive)
    (hz : z.Nonnegative) (hzle : relEntropy xstar z ≤ C)
    (hB : ∀ s, max (Real.exp 2 * xstar s) C < B) : clampBox B z = z := by
  refine clampBox_eq_of_mem (fun s => abs_le.mpr ⟨?_, ?_⟩)
  · have hub : z s ≤ max (Real.exp 2 * xstar s) C := relEntropy_coord_le hxs hz hzle s
    have hBpos : 0 < B :=
      lt_of_lt_of_le (mul_pos (Real.exp_pos 2) (hxs s)) (le_trans (le_max_left _ _) (hB s).le)
    have := hz s; linarith
  · exact le_of_lt (lt_of_le_of_lt (relEntropy_coord_le hxs hz hzle s) (hB s))

/-- **Confinement of the orbit to a relative-entropy sublevel set.** With `B` chosen past the
coercivity bound of the initial sublevel set, the cutoff orbit's relative entropy never
exceeds its initial value: a first-exit-from-the-box argument plus Lyapunov descent. -/
theorem orbit_relEntropy_le (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {B : ℝ} {Γ : ℝ → Concentration S} (hpos : ∀ t, 0 ≤ t → (Γ t).Positive)
    (hΓd : ∀ t, HasDerivAt Γ (N.massActionVectorField κ (clampBox B (Γ t))) t)
    (hB : ∀ s, max (Real.exp 2 * xstar s) (relEntropy xstar (Γ 0)) < B) :
    ∀ t, 0 ≤ t → relEntropy xstar (Γ t) ≤ relEntropy xstar (Γ 0) := by
  set C₀ := relEntropy xstar (Γ 0) with hC₀def
  have hdiff : Differentiable ℝ Γ := fun t => (hΓd t).differentiableAt
  have hhcont : Continuous (fun t => relEntropy xstar (Γ t)) :=
    (relEntropy_continuous hxs).comp hdiff.continuous
  have hcs : ∀ s, Continuous (fun t => Γ t s) := fun s => (continuous_apply s).comp hdiff.continuous
  have hBpos : ∀ s, 0 < B := fun s =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos 2) (hxs s)) (le_trans (le_max_left _ _) (hB s).le)
  have hchain : ∀ t, 0 < t → clampBox B (Γ t) = Γ t →
      HasDerivAt (fun τ => relEntropy xstar (Γ τ))
        (∑ s, (Real.log (Γ t s) - Real.log (xstar s)) * N.massActionVectorField κ (Γ t) s) t := by
    intro t htpos hcl
    have hΓdt : HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t := by rw [← hcl]; exact hΓd t
    exact relEntropy_hasDerivAt hxs (hpos t htpos.le) (fun s => (hasDerivAt_pi.mp hΓdt) s)
  have hanti : ∀ b : ℝ, (∀ t, 0 < t → t < b → clampBox B (Γ t) = Γ t) →
      AntitoneOn (fun τ => relEntropy xstar (Γ τ)) (Set.Icc 0 b) := by
    intro b hbox
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) hhcont.continuousOn ?_ ?_
    · intro t ht; rw [interior_Icc, Set.mem_Ioo] at ht
      exact (hchain t ht.1 (hbox t ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc, Set.mem_Ioo] at ht
      rw [(hchain t ht.1 (hbox t ht.1 ht.2)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.1.le) hxs hcb
  have hbox_all : ∀ t, 0 ≤ t → ∀ s, Γ t s < B := by
    intro tBad htBad sBad
    by_contra hge
    rw [not_lt] at hge
    set A : Set ℝ := {t | 0 ≤ t ∧ ∃ s, B ≤ Γ t s} with hA
    have hAne : A.Nonempty := ⟨tBad, htBad, sBad, hge⟩
    have hAcl : IsClosed A := by
      have heq : A = Set.Ici 0 ∩ ⋃ s, {t | B ≤ Γ t s} := by
        ext t; simp only [hA, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iUnion]
      rw [heq]
      exact isClosed_Ici.inter
        (isClosed_iUnion_of_finite fun s => isClosed_le continuous_const (hcs s))
    have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
    have ht₁A : sInf A ∈ A := hAcl.csInf_mem hAne hAbdd
    set t₁ := sInf A with ht₁def
    have ht₁0 : 0 ≤ t₁ := ht₁A.1
    obtain ⟨s₁, hs₁⟩ := ht₁A.2
    have hboxbefore : ∀ t, 0 < t → t < t₁ → clampBox B (Γ t) = Γ t := by
      intro t htpos htlt
      have hltB : ∀ s, Γ t s < B := by
        intro s
        by_contra hge
        rw [not_lt] at hge
        exact absurd (csInf_le hAbdd ⟨htpos.le, s, hge⟩) (not_le.mpr htlt)
      refine clampBox_eq_of_mem (fun s => abs_le.mpr ⟨?_, le_of_lt (hltB s)⟩)
      have := (hpos t htpos.le) s; have := hBpos s; linarith
    have hht₁ : relEntropy xstar (Γ t₁) ≤ C₀ :=
      hanti t₁ hboxbefore (Set.left_mem_Icc.mpr ht₁0) (Set.right_mem_Icc.mpr ht₁0) ht₁0
    have hcoer : Γ t₁ s₁ ≤ max (Real.exp 2 * xstar s₁) C₀ :=
      relEntropy_coord_le hxs (hpos t₁ ht₁0).nonnegative hht₁ s₁
    exact absurd hs₁ (not_le.mpr (lt_of_le_of_lt hcoer (hB s₁)))
  intro t ht
  have hclamp_all : ∀ τ, 0 < τ → τ < t → clampBox B (Γ τ) = Γ τ := by
    intro τ hτpos _
    refine clampBox_eq_of_mem (fun s => abs_le.mpr ⟨?_, le_of_lt (hbox_all τ hτpos.le s)⟩)
    have := (hpos τ hτpos.le) s; have := hBpos s; linarith
  exact hanti t hclamp_all (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht

/-- **Linear lower bound on the mass-action field over a box.** On the nonnegative part of
the box `[0,B]^S`, each component satisfies `f_s(x) ≥ −L·x_s` for a uniform `L ≥ 0`. Every
reaction that decreases `x_s` consumes `s`, so its monomial carries a factor of `x_s`; on the
box the cofactor is bounded by `(max 1 B)^{deg}`. -/
theorem exists_field_lower_bound (N : Network S) (κ : N.RateConstants) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : Concentration S, x.Nonnegative → (∀ s, x s ≤ B) →
      ∀ s, -(L * x s) ≤ N.massActionVectorField κ x s := by
  have hBmnn : (0:ℝ) ≤ max 1 B := le_trans zero_le_one (le_max_left _ _)
  have hBm1 : (1:ℝ) ≤ max 1 B := le_max_left _ _
  refine ⟨∑ s', ∑ r : N.R,
      κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'|, ?_, ?_⟩
  · refine Finset.sum_nonneg fun s' _ => Finset.sum_nonneg fun r _ => ?_
    exact mul_nonneg (mul_nonneg (κ.positive r).le (pow_nonneg hBmnn _)) (abs_nonneg _)
  · intro x hx hxB s
    rw [massActionVectorField_apply]
    have hxle : ∀ s', x s' ≤ max 1 B := fun s' => le_trans (hxB s') (le_max_right 1 B)
    have hcoef_nn : ∀ r : N.R,
        0 ≤ κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| :=
      fun r => mul_nonneg (mul_nonneg (κ.positive r).le (pow_nonneg hBmnn _)) (abs_nonneg _)
    have hterm : ∀ r : N.R,
        -(κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| * x s)
          ≤ N.massActionRate κ r x * N.reactionVector r s := by
      intro r
      by_cases hΔ : 0 ≤ N.reactionVector r s
      · have h1 : 0 ≤ N.massActionRate κ r x * N.reactionVector r s :=
          mul_nonneg (N.massActionRate_nonneg κ r hx) hΔ
        have h2 : 0 ≤ κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') *
            |N.reactionVector r s| * x s := mul_nonneg (hcoef_nn r) (hx s)
        linarith
      · rw [not_le] at hΔ
        -- consuming reaction: factor out `x s`
        have hts : (N.reaction r).target s < (N.reaction r).source s := by
          rw [reactionVector_apply] at hΔ
          have : ((N.reaction r).target s : ℝ) < ((N.reaction r).source s : ℝ) := by linarith
          exact_mod_cast this
        have hsrc1 : 1 ≤ (N.reaction r).source s := by omega
        have hmono_eq : (N.reaction r).source.massActionMonomial x
            = x s * (x s ^ ((N.reaction r).source s - 1)
                * ∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s') := by
          have h1 : (N.reaction r).source.massActionMonomial x
              = x s ^ (N.reaction r).source s
                * ∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s' := by
            show (∏ s', x s' ^ (N.reaction r).source s') = _
            exact (Finset.mul_prod_erase Finset.univ
              (fun s' => x s' ^ (N.reaction r).source s') (Finset.mem_univ s)).symm
          rw [h1]
          have h2 : x s ^ (N.reaction r).source s = x s * x s ^ ((N.reaction r).source s - 1) := by
            conv_lhs => rw [show (N.reaction r).source s = ((N.reaction r).source s - 1) + 1 from by omega]
            rw [pow_succ']
          rw [h2, mul_assoc]
        set P := x s ^ ((N.reaction r).source s - 1)
          * ∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s' with hP
        have hPnn : 0 ≤ P :=
          mul_nonneg (pow_nonneg (hx s) _) (Finset.prod_nonneg fun s' _ => pow_nonneg (hx s') _)
        have hPle : P ≤ (max 1 B) ^ (∑ s'', (N.reaction r).source s'') := by
          have h1 : x s ^ ((N.reaction r).source s - 1) ≤ (max 1 B) ^ ((N.reaction r).source s - 1) :=
            pow_le_pow_left₀ (hx s) (hxle s) _
          have h2 : (∏ s' ∈ Finset.univ.erase s, x s' ^ (N.reaction r).source s')
              ≤ ∏ s' ∈ Finset.univ.erase s, (max 1 B) ^ (N.reaction r).source s' :=
            Finset.prod_le_prod₀ (fun s' _ => pow_nonneg (hx s') _)
              (fun s' _ => pow_le_pow_left₀ (hx s') (hxle s') _)
          have hsum_eq : (N.reaction r).source s + ∑ s' ∈ Finset.univ.erase s, (N.reaction r).source s'
              = ∑ s'', (N.reaction r).source s'' :=
            Finset.add_sum_erase Finset.univ (fun s' => (N.reaction r).source s') (Finset.mem_univ s)
          calc P ≤ (max 1 B) ^ ((N.reaction r).source s - 1)
                    * ∏ s' ∈ Finset.univ.erase s, (max 1 B) ^ (N.reaction r).source s' :=
                mul_le_mul h1 h2 (Finset.prod_nonneg fun s' _ => pow_nonneg (hx s') _)
                  (pow_nonneg hBmnn _)
            _ = (max 1 B) ^ ((N.reaction r).source s - 1
                  + ∑ s' ∈ Finset.univ.erase s, (N.reaction r).source s') := by
                rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
            _ ≤ (max 1 B) ^ (∑ s'', (N.reaction r).source s'') :=
                pow_le_pow_right₀ hBm1 (by omega)
        have hrate_eq : N.massActionRate κ r x = κ.k r * (x s * P) := by
          show κ.k r * (N.reaction r).source.massActionMonomial x = κ.k r * (x s * P)
          rw [hmono_eq]
        have hkey : -(κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|)
            ≤ κ.k r * P * N.reactionVector r s := by
          have hPbound : κ.k r * P ≤ κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') :=
            mul_le_mul_of_nonneg_left hPle (κ.positive r).le
          have hRHS : κ.k r * P * N.reactionVector r s
              = -(κ.k r * P * |N.reactionVector r s|) := by rw [abs_of_neg hΔ]; ring
          rw [hRHS]
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_right hPbound (abs_nonneg _)
        have e1 : -(κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| * x s)
            = x s * -(κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|) := by
          ring
        have e2 : x s * (κ.k r * P * N.reactionVector r s)
            = N.massActionRate κ r x * N.reactionVector r s := by rw [hrate_eq]; ring
        rw [e1, ← e2]
        exact mul_le_mul_of_nonneg_left hkey (hx s)
    have hinner_le : (∑ r : N.R,
          κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|)
        ≤ ∑ s', ∑ r : N.R,
          κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'| :=
      Finset.single_le_sum
        (f := fun s' => ∑ r : N.R,
          κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'|)
        (fun s' _ => Finset.sum_nonneg fun r _ =>
          mul_nonneg (mul_nonneg (κ.positive r).le (pow_nonneg hBmnn _)) (abs_nonneg _))
        (Finset.mem_univ s)
    calc -((∑ s', ∑ r : N.R,
            κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s'|) * x s)
        ≤ -((∑ r : N.R,
            κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s|) * x s) := by
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_right hinner_le (hx s)
      _ = ∑ r : N.R,
            -(κ.k r * (max 1 B) ^ (∑ s'', (N.reaction r).source s'') * |N.reactionVector r s| * x s) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      _ ≤ ∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s :=
          Finset.sum_le_sum fun r _ => hterm r

/-- **Local asymptotic stability of the complex-balanced equilibrium.** For a weakly
reversible network, a positive complex-balanced reference `x*`, and a positive start `x₀` in
the same compatibility class whose relative entropy lies below every reference coordinate,
the mass-action semiflow built from the bounded-Lipschitz cutoff has the genuine dynamics as
its orbit through `x₀`, and that orbit's ω-limit set is exactly `{x*}`. -/
theorem omegaLimit_eq_singleton_of_local
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hx0 : x₀.Positive) (hx0compat : N.StoichCompatible x₀ xstar)
    (hloc : ∀ s, relEntropy xstar x₀ < xstar s) :
    ∃ (ϕ : Flow ℝ≥0 (Concentration S)) (γ : Concentration S → ℝ → Concentration S),
      (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t) ∧
      omegaLimit atTop ϕ {x₀} = {xstar} := by
  set C₀ := relEntropy xstar x₀ with hC₀
  -- choose B past the coercivity bound of the initial sublevel set
  set B : ℝ := 1 + |C₀| + ∑ s, Real.exp 2 * xstar s with hBdef
  have hsumnn : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hBnn : 0 ≤ B := by rw [hBdef]; have := abs_nonneg C₀; linarith
  have hBbig : ∀ s, max (Real.exp 2 * xstar s) C₀ < B := by
    intro s
    have hsum : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le) (Finset.mem_univ s)
    rw [max_lt_iff, hBdef]
    exact ⟨by linarith [abs_nonneg C₀], by linarith [le_abs_self C₀]⟩
  -- the field's linear lower bound, the cutoff, and the resulting semiflow
  obtain ⟨L, hLnn, hbound⟩ := N.exists_field_lower_bound κ B
  obtain ⟨Klip, M, hlip, hbd⟩ := N.exists_cutoff κ hBnn
  obtain ⟨ϕ, γ, hγ0, hγd, hϕγ⟩ := ODE.exists_flow hlip hbd
  have hΓd : ∀ t, HasDerivAt (γ x₀) (N.massActionVectorField κ (clampBox B (γ x₀ t))) t :=
    fun t => hγd x₀ t
  have hΓ0pos : Concentration.Positive (γ x₀ 0) := by rw [hγ0]; exact hx0
  have hpos : ∀ t, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    orbit_pos N κ hBnn hLnn hbound hΓ0pos hΓd
  have hrele : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C₀ := by
    have hB' : ∀ s, max (Real.exp 2 * xstar s) (relEntropy xstar (γ x₀ 0)) < B := by
      intro s; rw [hγ0]; exact hBbig s
    intro t ht
    have := orbit_relEntropy_le N κ hxs hcb hpos hΓd hB' t ht
    rw [hγ0, ← hC₀] at this; exact this
  have hclamp : ∀ t, 0 ≤ t → clampBox B (γ x₀ t) = γ x₀ t := fun t ht =>
    clampBox_eq_of_sublevel hxs (hpos t ht).nonnegative (hrele t ht) hBbig
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht; have := hΓd t; rwa [hclamp t ht] at this
  -- the compact, positively-confined sublevel set absorbing the orbit
  set K : Set (Concentration S) := {y | y.Nonnegative ∧ relEntropy xstar y ≤ C₀} with hK
  have hKcpt : IsCompact K := isCompact_relEntropy_sublevel hxs C₀
  have horbitK : ∀ t : ℝ≥0, ϕ t x₀ ∈ K := by
    intro t; rw [hϕγ]
    exact ⟨(hpos t t.coe_nonneg).nonnegative, hrele t t.coe_nonneg⟩
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbitK t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK⟩
  -- Lyapunov descent along the orbit (monotonicity for LaSalle)
  have hAnti : AntitoneOn (fun t => relEntropy xstar (γ x₀ t)) (Set.Ici 0) := by
    have hcont : Continuous (fun t => relEntropy xstar (γ x₀ t)) :=
      (relEntropy_continuous hxs).comp (Differentiable.continuous fun t => (hΓd t).differentiableAt)
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn ?_ ?_
    · intro t ht; rw [interior_Ici, Set.mem_Ioi] at ht
      exact (relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(relEntropy_hasDerivAt hxs (hpos t ht.le)
        (fun s => (hasDerivAt_pi.mp (hsol t ht.le)) s)).deriv]
      exact dissipation_nonpos N κ (hpos t ht.le) hxs hcb
  have hmono : ∀ a b : ℝ≥0, a ≤ b →
      relEntropy xstar (ϕ b x₀) ≤ relEntropy xstar (ϕ a x₀) := by
    intro a b hab
    rw [hϕγ, hϕγ]
    exact hAnti (Set.mem_Ici.mpr a.coe_nonneg) (Set.mem_Ici.mpr b.coe_nonneg) (by exact_mod_cast hab)
  obtain ⟨c, _, hωinv, hωc⟩ :=
    Flow.laSalle ϕ (relEntropy_continuous hxs) x₀ hKcpt habs hmono
  have hωne : (omegaLimit atTop ϕ {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hKcpt habs (Set.singleton_nonempty x₀)
  -- ω ⊆ K
  have hωK : omegaLimit atTop ϕ {x₀} ⊆ K :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ) univ_mem).trans
      ((IsClosed.closure_subset_iff hKcpt.isClosed).mpr hsubK)
  -- ω lies in the affine compatibility class of x₀
  have hSclosed : IsClosed (N.stoichSubspace : Set (Concentration S)) :=
    N.stoichSubspace.closed_of_finiteDimensional
  have haffclosed : IsClosed {z : Concentration S | z - x₀ ∈ N.stoichSubspace} :=
    IsClosed.preimage (continuous_id.sub continuous_const) hSclosed
  have horbit_aff : ∀ t : ℝ≥0, ϕ t x₀ - x₀ ∈ N.stoichSubspace := by
    intro t; rw [hϕγ]
    have hsol' : ∀ τ ∈ Set.Icc (0:ℝ) ↑t,
        HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ τ)) τ := fun τ hτ => hsol τ hτ.1
    have := sub_mem_stoichSubspace_of_solution N κ t.coe_nonneg hsol'
    rwa [hγ0] at this
  have hωaff : omegaLimit atTop ϕ {x₀} ⊆ {z | z - x₀ ∈ N.stoichSubspace} := by
    refine (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ) univ_mem).trans ?_
    refine (IsClosed.closure_subset_iff haffclosed).mpr ?_
    rintro z ⟨t, -, x, hx, rfl⟩; rw [Set.mem_singleton_iff] at hx; subst hx; exact horbit_aff t
  -- every ω-point equals x*
  have hxstarmem : xstar ∈ N.positiveCompatibilityClass x₀ := ⟨hx0compat, hxs⟩
  have hsub : omegaLimit atTop ϕ {x₀} ⊆ {xstar} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    have hyK : y ∈ K := hωK hy
    have hyaff : y - x₀ ∈ N.stoichSubspace := hωaff hy
    -- positivity at any orbit point of `y`
    have hpos_of : ∀ z : Concentration S, z.Nonnegative → relEntropy xstar z ≤ C₀ → z.Positive := by
      intro z hznn hzle s
      rcases lt_or_eq_of_le (hznn s) with h | h
      · exact h
      · exact absurd (le_trans (relEntropy_ge_of_coord_zero hxs hznn h.symm) hzle)
          (not_le.mpr (hloc s))
    -- orbit of `y` stays in ω, hence in K, with constant relative entropy `c`
    have hyKt : ∀ t : ℝ, 0 ≤ t → γ y t ∈ K := by
      intro t ht; have := hωK (hωinv (NNReal.mk t ht) hy); rwa [hϕγ] at this
    have hconst : ∀ t : ℝ, 0 ≤ t → relEntropy xstar (γ y t) = c := by
      intro t ht; have := hωc _ (hωinv (NNReal.mk t ht) hy); rwa [hϕγ] at this
    have hyt_eq : ∀ t₀ : ℝ, 0 < t₀ → γ y t₀ = xstar := by
      intro t₀ ht₀
      have hclt : clampBox B (γ y t₀) = γ y t₀ :=
        clampBox_eq_of_sublevel hxs (hyKt t₀ ht₀.le).1 (hyKt t₀ ht₀.le).2 hBbig
      have hydt : HasDerivAt (γ y) (N.massActionVectorField κ (γ y t₀)) t₀ := by
        rw [← hclt]; exact hγd y t₀
      have hposy : Concentration.Positive (γ y t₀) := hpos_of _ (hyKt t₀ ht₀.le).1 (hyKt t₀ ht₀.le).2
      -- dissipation vanishes: relative entropy is locally constant
      have hchain := relEntropy_hasDerivAt hxs hposy (fun s => (hasDerivAt_pi.mp hydt) s)
      have heqc : (fun τ => relEntropy xstar (γ y τ)) =ᶠ[𝓝 t₀] (fun _ => c) := by
        filter_upwards [Ioi_mem_nhds ht₀] with τ hτ; exact hconst τ (le_of_lt hτ)
      have hd0 : HasDerivAt (fun τ => relEntropy xstar (γ y τ)) 0 t₀ :=
        (heqc.hasDerivAt_iff).mpr (hasDerivAt_const t₀ c)
      have hdiss : (∑ s, (Real.log (γ y t₀ s) - Real.log (xstar s))
          * N.massActionVectorField κ (γ y t₀) s) = 0 := hchain.unique hd0
      have hCB : N.IsComplexBalanced κ (γ y t₀) :=
        complexBalanced_of_dissipation_eq_zero N κ hposy hxs hcb hdiss
      -- and it lies in x₀'s positive class
      have hmem : γ y t₀ ∈ N.positiveCompatibilityClass x₀ := by
        refine ⟨?_, hposy⟩
        show γ y t₀ - x₀ ∈ N.stoichSubspace
        have h1 : γ y t₀ - y ∈ N.stoichSubspace := by
          have hsoly : ∀ τ ∈ Set.Icc (0:ℝ) t₀,
              HasDerivAt (γ y) (N.massActionVectorField κ (γ y τ)) τ := by
            intro τ hτ
            have hcl : clampBox B (γ y τ) = γ y τ :=
              clampBox_eq_of_sublevel hxs (hyKt τ hτ.1).1 (hyKt τ hτ.1).2 hBbig
            rw [← hcl]; exact hγd y τ
          have := sub_mem_stoichSubspace_of_solution N κ ht₀.le hsoly
          rwa [hγ0] at this
        have heq : γ y t₀ - x₀ = (γ y t₀ - y) + (y - x₀) := by ring
        rw [heq]; exact N.stoichSubspace.add_mem h1 hyaff
      exact N.isComplexBalanced_unique_in_positiveClass hwr κ hmem hxstarmem hCB hcb
    -- pass to the limit `t₀ → 0⁺`
    have hγycont : Continuous (γ y) :=
      Differentiable.continuous fun t => (hγd y t).differentiableAt
    have htend1 : Tendsto (γ y) (𝓝[>] (0:ℝ)) (𝓝 y) := by
      have : Tendsto (γ y) (𝓝[>] (0:ℝ)) (𝓝 (γ y 0)) :=
        hγycont.continuousAt.continuousWithinAt
      rwa [hγ0] at this
    have htend2 : Tendsto (γ y) (𝓝[>] (0:ℝ)) (𝓝 xstar) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact (hyt_eq τ hτ).symm
    exact tendsto_nhds_unique htend1 htend2
  refine ⟨ϕ, γ, hγ0, hϕγ, hsol, ?_⟩
  exact (Set.subset_singleton_iff_eq.mp hsub).resolve_left hωne.ne_empty

end Network

end CRNT
