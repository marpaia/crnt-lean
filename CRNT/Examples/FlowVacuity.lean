import CRNT.Dynamics.GlobalPersistence
import CRNT.Dynamics.GlobalPermanence
import CRNT.Dynamics.SingleLinkageGAC

/-!
# Flow-based persistence and permanence are vacuous without a global flow

`IsMassActionFlow κ ϕ γ` asks for a flow on all of `ℝ^S` whose curves solve the mass-action
equations from every initial point, including points outside the nonnegative orthant. For
`2X → 0` the equation `x' = −2κ x²` blows up in finite time from `x(0) = −1`, so no such flow
exists (`no_massActionFlow`). Consequently the flow-based properties `StructurallyPersistentStd`
and `StructurallyPermanent` hold vacuously for this network (`structurallyPersistentStd`,
`structurallyPermanent`), although its positive solutions `x(t) = 1/(1 + 2κ t)` tend to `0`, so
the trajectory-based `StructurallyPersistent` fails (`not_structurallyPersistent`).

The same holds for every network with a reaction whose source has total molecularity at least two
in a species it consumes, so statements whose conclusion is `StructurallyPersistentStd` or
`StructurallyPermanent` (including `PersistenceConjecture`) carry content only for networks
admitting a global flow; the trajectory-based forms (`PersistentFrom`, `StructurallyPersistent`,
`StronglyEndotacticStd.permanent_trajectories`) do not have this restriction.
-/

open Filter Set
open scoped NNReal Topology

namespace CRNT
namespace Examples
namespace FlowVacuity

open Network

/-- The complex `2X`. -/
def twoX : Complex Unit := fun _ => 2

/-- `2X → 0`. -/
abbrev net : Network Unit := ⟨Unit, inferInstance, inferInstance, fun _ => ⟨twoX, 0⟩⟩

theorem field_eq (κ : RateConstants net) (x : Concentration Unit) :
    net.massActionVectorField κ x () = -2 * κ.k () * x () ^ 2 := by
  rw [massActionVectorField_apply]
  simp [massActionRate, Network.reactionVector, Complex.massActionMonomial, twoX]
  ring

/-- **No mass-action flow exists**: from `x(0) = −1`, `−1/x(t) + 2κ t` is constant while `x` is
nonincreasing, which is impossible at `t = 1/κ`. -/
theorem no_massActionFlow (κ : RateConstants net) (ϕ : Flow ℝ≥0 (Concentration Unit))
    (γ : Concentration Unit → ℝ → Concentration Unit) : ¬ net.IsMassActionFlow κ ϕ γ := by
  rintro ⟨hzero, -, hsol⟩
  set x₀ : Concentration Unit := fun _ => -1
  set y : ℝ → ℝ := fun t => γ x₀ t ()
  have hk := κ.positive ()
  have hy : ∀ t, 0 ≤ t → HasDerivAt y (-2 * κ.k () * y t ^ 2) t := by
    intro t ht
    have := (hasDerivAt_pi.mp (hsol x₀ t ht)) ()
    rw [field_eq] at this
    exact this
  have hy0 : y 0 = -1 := by simp [y, hzero, x₀]
  -- `y` is nonincreasing, so `y ≤ −1`
  have hanti : AntitoneOn y (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hy t ht).continuousAt.continuousWithinAt)
      (fun t ht => by rw [interior_Ici] at ht ⊢; exact (hy t (le_of_lt ht)).hasDerivWithinAt)
      (fun t ht => by
        have : 0 ≤ κ.k () * y t ^ 2 := mul_nonneg hk.le (sq_nonneg _)
        linarith)
  have hyle : ∀ t, 0 ≤ t → y t ≤ -1 := fun t ht => by
    have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    rw [hy0] at this; exact this
  -- `h(t) = −1/y(t) + 2κ t` is constant
  set h : ℝ → ℝ := fun t => -(y t)⁻¹ + 2 * κ.k () * t
  have hh : ∀ t, 0 ≤ t → HasDerivAt h 0 t := by
    intro t ht
    have hyne : y t ≠ 0 := by linarith [hyle t ht]
    have h1 := ((hy t ht).inv hyne).neg
    have h2 := ((hasDerivAt_id t).const_mul (2 * κ.k ()))
    have h3 := h1.add h2
    have hfun : h = (-y⁻¹) + fun s => 2 * κ.k () * id s := by
      funext s; simp [h]
    rw [hfun]
    convert h3 using 1
    field_simp
    ring
  have hhanti : AntitoneOn h (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => by rw [interior_Ici] at ht ⊢; exact (hh t (le_of_lt ht)).hasDerivWithinAt)
      (fun _ _ => le_rfl)
  set T := (κ.k ())⁻¹
  have hT : 0 ≤ T := (inv_pos.mpr hk).le
  have hhT := hhanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT
  simp only [h, hy0, mul_zero, add_zero, T] at hhT
  have hkT : 2 * κ.k () * (κ.k ())⁻¹ = 2 := by field_simp
  rw [hkT] at hhT
  -- so `1/y(T) ≥ 1`, contradicting `y(T) ≤ −1`
  have hyT := hyle T hT
  have hinv : (y T)⁻¹ < 0 := inv_lt_zero.mpr (by linarith)
  norm_num at hhT
  linarith

/-- The flow-based persistence property holds vacuously. -/
theorem structurallyPersistentStd : net.StructurallyPersistentStd :=
  fun κ ϕ γ hflow => absurd hflow (no_massActionFlow κ ϕ γ)

/-- The flow-based permanence property holds vacuously. -/
theorem structurallyPermanent : net.StructurallyPermanent :=
  fun κ ϕ γ hflow => absurd hflow (no_massActionFlow κ ϕ γ)

/-- **The positive solutions tend to `0`**, so the trajectory-based property fails. -/
theorem not_structurallyPersistent : ¬ net.StructurallyPersistent := by
  intro h
  let κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩
  have hx₀ : Concentration.Positive (fun _ : Unit => (1 : ℝ)) := fun _ => one_pos
  obtain ⟨K₀, hK₀c, hK₀pos, hK₀⟩ := h κ (fun _ => 1) hx₀
  set Γ : ℝ → Concentration Unit := fun t _ => (1 + 2 * t)⁻¹
  have hsol : ∀ t, 0 ≤ t → HasDerivAt Γ (net.massActionVectorField κ (Γ t)) t := by
    intro t ht
    rw [hasDerivAt_pi]
    intro u
    rw [show u = () from rfl, field_eq]
    have hne : 1 + 2 * t ≠ 0 := by linarith
    show HasDerivAt (fun τ : ℝ => (1 + 2 * τ)⁻¹) (-2 * κ.k () * ((1 + 2 * t)⁻¹) ^ 2) t
    have h1 : HasDerivAt (fun τ : ℝ => 1 + 2 * τ) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add 1
    convert h1.inv hne using 1
    simp only [κ]
    field_simp
  have hin : ∀ t, 0 ≤ t → Γ t ∈ K₀ := hK₀ Γ (by funext u; simp [Γ]) hsol
  obtain ⟨y₀, hy₀, hmin⟩ := hK₀c.exists_isMinOn ⟨Γ 0, hin 0 le_rfl⟩
    (continuous_apply ()).continuousOn
  have hε := hK₀pos y₀ hy₀ ()
  set ε := y₀ ()
  -- choose `t` with `1/(1 + 2t) < ε`
  set t := ε⁻¹
  have ht : 0 ≤ t := (inv_pos.mpr hε).le
  have hle : ε ≤ (1 + 2 * t)⁻¹ := hmin (hin t ht)
  have h1 : (1 + 2 * t)⁻¹ < ε := by
    rw [inv_lt_comm₀ (by positivity) hε]
    simp only [t]; linarith [inv_pos.mpr hε]
  linarith

end FlowVacuity
end Examples
end CRNT
