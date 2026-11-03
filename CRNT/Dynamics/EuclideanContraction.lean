import CRNT.Dynamics.OrthantMonotone
import CRNT.Kinetics.MassActionJacobian

/-!
# Contraction in the Euclidean norm (logarithmic-norm criterion)

If on a convex set `C` the Jacobian of a vector field satisfies `⟨u, J(x) u⟩ ≤ −c |u|²` (the
Euclidean logarithmic norm `μ₂(J(x)) ≤ −c`), then any two solutions staying in `C` approach each
other exponentially: `|x(t) − y(t)|² ≤ e^{−2ct} |x(0) − y(0)|²` (`contraction_of_jacobian`).
For mass-action systems: `massAction_contraction`.
-/

open Set
open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [Fintype S]

/-- The squared Euclidean distance. -/
noncomputable def sqDist (x y : S → ℝ) : ℝ := ∑ s, (x s - y s) ^ 2

/-- **One-sided Lipschitz bound from the Jacobian.** -/
theorem oneSided_of_jacobian {f : (S → ℝ) → (S → ℝ)} {J : (S → ℝ) → ((S → ℝ) →L[ℝ] (S → ℝ))}
    {C : Set (S → ℝ)} (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (J x) x) {c : ℝ}
    (hJ : ∀ x ∈ C, ∀ u : S → ℝ, ∑ s, u s * J x u s ≤ -c * ∑ s, u s ^ 2)
    {a b : S → ℝ} (ha : a ∈ C) (hb : b ∈ C) :
    ∑ s, (a s - b s) * (f a s - f b s) ≤ -c * sqDist a b := by
  set u : S → ℝ := a - b
  set z : ℝ → (S → ℝ) := fun τ => b + τ • u
  have hz : ∀ τ ∈ Icc (0 : ℝ) 1, z τ ∈ C := by
    intro τ hτ
    have : z τ = (1 - τ) • b + τ • a := by
      funext s; simp [z, u]; ring
    rw [this]
    exact hC hb ha (by linarith [hτ.2]) hτ.1 (by ring)
  set g : ℝ → ℝ := fun τ => ∑ s, u s * f (z τ) s
  have hzd : ∀ τ, HasDerivAt z u τ := by
    intro τ
    have := ((hasDerivAt_id τ).smul_const u).const_add b
    simpa [z] using this
  have hgd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt g (∑ s, u s * J (z τ) u s) τ := by
    intro τ hτ
    have hcomp : HasDerivAt (fun τ => f (z τ)) (J (z τ) u) τ :=
      (hf (z τ) (hz τ hτ)).comp_hasDerivAt τ (hzd τ)
    have := HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
      ((hasDerivAt_pi.mp hcomp) s).const_mul (u s)
    simpa [g] using this
  -- `g(τ) + c |u|² τ` is antitone on `[0, 1]`
  set W : ℝ → ℝ := fun τ => g τ + c * (∑ s, u s ^ 2) * τ
  have hWanti : AntitoneOn W (Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun τ hτ => ?_) (fun τ hτ => ?_) (fun τ hτ => ?_)
      (f' := fun τ => ∑ s, u s * J (z τ) u s + c * (∑ s, u s ^ 2) * 1)
    · exact ((hgd τ hτ).add ((hasDerivAt_id τ).const_mul _)).continuousAt.continuousWithinAt
    · rw [interior_Icc] at hτ
      exact ((hgd τ (Ioo_subset_Icc_self hτ)).add
        ((hasDerivAt_id τ).const_mul _)).hasDerivWithinAt
    · rw [interior_Icc] at hτ
      have := hJ (z τ) (hz τ (Ioo_subset_Icc_self hτ)) u
      linarith
  have h01 := hWanti (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [W, g, mul_zero, add_zero, mul_one] at h01
  have hz0 : z 0 = b := by simp [z]
  have hz1 : z 1 = a := by funext s; simp [z, u]
  rw [hz0, hz1] at h01
  have hsum : ∑ s, (a s - b s) * (f a s - f b s) = ∑ s, u s * f a s - ∑ s, u s * f b s := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by simp [u]; ring
  rw [hsum]
  have hsd : sqDist a b = ∑ s, u s ^ 2 := by simp [sqDist, u]
  rw [hsd]
  linarith

/-- **Exponential contraction.** -/
theorem contraction_of_jacobian {f : (S → ℝ) → (S → ℝ)} {J : (S → ℝ) → ((S → ℝ) →L[ℝ] (S → ℝ))}
    {C : Set (S → ℝ)} (hC : Convex ℝ C) (hf : ∀ x ∈ C, HasFDerivAt f (J x) x) {c : ℝ}
    (hJ : ∀ x ∈ C, ∀ u : S → ℝ, ∑ s, u s * J x u s ≤ -c * ∑ s, u s ^ 2)
    {x y : ℝ → (S → ℝ)} (hx : ∀ t, 0 ≤ t → HasDerivAt x (f (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (f (y t)) t)
    (hxC : ∀ t, 0 ≤ t → x t ∈ C) (hyC : ∀ t, 0 ≤ t → y t ∈ C) :
    ∀ t, 0 ≤ t → sqDist (x t) (y t) ≤ Real.exp (-(2 * c * t)) * sqDist (x 0) (y 0) := by
  set V : ℝ → ℝ := fun t => sqDist (x t) (y t)
  have hVd : ∀ t, 0 ≤ t →
      HasDerivAt V (∑ s, 2 * (x t s - y t s) * (f (x t) s - f (y t) s)) t := by
    intro t ht
    have := HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
      ((((hasDerivAt_pi.mp (hx t ht)) s).sub ((hasDerivAt_pi.mp (hy t ht)) s)).pow 2)
    convert this using 1
    · funext τ; simp [V, sqDist]
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp
  set W : ℝ → ℝ := fun t => Real.exp (2 * c * t) * V t
  have hWd : ∀ t, 0 ≤ t → HasDerivAt W (Real.exp (2 * c * t) * (2 * c) * V t +
      Real.exp (2 * c * t) * ∑ s, 2 * (x t s - y t s) * (f (x t) s - f (y t) s)) t := by
    intro t ht
    have he : HasDerivAt (fun t => Real.exp (2 * c * t)) (Real.exp (2 * c * t) * (2 * c)) t := by
      have := ((hasDerivAt_id t).const_mul (2 * c)).exp
      simpa using this
    exact he.mul (hVd t ht)
  have hWanti : AntitoneOn W (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hWd t ht).continuousAt.continuousWithinAt)
      (fun t ht => by rw [interior_Ici] at ht ⊢; exact (hWd t (le_of_lt ht)).hasDerivWithinAt)
      (fun t ht => ?_)
    rw [interior_Ici] at ht
    have hone := oneSided_of_jacobian hC hf hJ (hxC t ht.le) (hyC t ht.le)
    have hsum : ∑ s, 2 * (x t s - y t s) * (f (x t) s - f (y t) s) =
        2 * ∑ s, (x t s - y t s) * (f (x t) s - f (y t) s) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsum]
    have hpos := Real.exp_pos (2 * c * t)
    have : V t = sqDist (x t) (y t) := rfl
    nlinarith
  intro t ht
  have h := hWanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  simp only [W, mul_zero, Real.exp_zero, one_mul] at h
  have hexp : Real.exp (-(2 * c * t)) * Real.exp (2 * c * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc sqDist (x t) (y t) = Real.exp (-(2 * c * t)) * (Real.exp (2 * c * t) * V t) := by
        rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (-(2 * c * t)) * V 0 :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

variable [DecidableEq S]

/-- **Contraction of mass-action systems.** -/
theorem massAction_contraction (N : Network S) (κ : N.RateConstants) {C : Set (Concentration S)}
    (hC : Convex ℝ C) {c : ℝ}
    (hJ : ∀ x ∈ C, ∀ u : S → ℝ, ∑ s, u s * N.massActionJacobianCLM κ x u s ≤ -c * ∑ s, u s ^ 2)
    {x y : ℝ → Concentration S}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hy : ∀ t, 0 ≤ t → HasDerivAt y (N.massActionVectorField κ (y t)) t)
    (hxC : ∀ t, 0 ≤ t → x t ∈ C) (hyC : ∀ t, 0 ≤ t → y t ∈ C) :
    ∀ t, 0 ≤ t → sqDist (x t) (y t) ≤ Real.exp (-(2 * c * t)) * sqDist (x 0) (y 0) :=
  contraction_of_jacobian hC (fun x _ => N.massActionVectorField_hasFDerivAt κ x) hJ hx hy hxC hyC

end Network
end CRNT
