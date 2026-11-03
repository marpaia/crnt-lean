import CRNT.Oscillation.PlanarFrontier
import CRNT.Oscillation.SimpleCycle

/-!
# Differential calculus for Bendixson--Dulac certificates

The full Bendixson--Dulac theorem still needs a planar Green/Stokes argument.  This module closes the
local calculus side so certificate producers do not have to reason through `deriv` manually.  In
particular it proves the coordinate product rule for the scaled field `B(x) f(x)` and gives an exact
formula for its divergence from four coordinate derivatives.
-/

namespace CRNT

namespace Planar

/-- Replacing a coordinate by its current value leaves a planar point unchanged. -/
@[simp] theorem setCoord_self (x : Phase2) (i : Fin 2) : setCoord x i (x i) = x := by
  ext j
  by_cases h : j = i
  · subst j
    simp [setCoord]
  · simp [setCoord, Function.update_of_ne h]

/-- A proof-relevant coordinate partialDeriv derivative. -/
def HasPartialAt (g : Phase2 → ℝ) (i : Fin 2) (x : Phase2) (dg : ℝ) : Prop :=
  HasDerivAt (fun a => g (setCoord x i a)) dg (x i)

/-- A certified coordinate derivative agrees with the classical `partialDeriv` used by the Dulac API. -/
theorem HasPartialAt.partial_eq
    {g : Phase2 → ℝ} {i : Fin 2} {x : Phase2} {dg : ℝ}
    (h : HasPartialAt g i x dg) : partialDeriv g i x = dg := by
  unfold partialDeriv HasPartialAt at *
  exact h.deriv

/-- Coordinate product rule. -/
theorem HasPartialAt.mul
    {g h : Phase2 → ℝ} {i : Fin 2} {x : Phase2} {dg dh : ℝ}
    (hg : HasPartialAt g i x dg) (hh : HasPartialAt h i x dh) :
    HasPartialAt (fun y => g y * h y) i x (dg * h x + g x * dh) := by
  unfold HasPartialAt at *
  -- `HasDerivAt.mul` gives the pointwise-product function, and leaves `setCoord x i (x i)`
  -- unsimplified in the derivative; rewrite that to `x` first.
  have hsame : setCoord x i (x i) = x := setCoord_self x i
  have hp := hg.mul hh
  rw [hsame] at hp
  exact hp

/-- Coordinate product rule for one component of a Dulac-scaled vector field. -/
theorem partial_scaled_component
    {B : Phase2 → ℝ} {field : Phase2 → Phase2}
    {i : Fin 2} {x : Phase2} {dB dF : ℝ}
    (hB : HasPartialAt B i x dB)
    (hF : HasPartialAt (fun y => field y i) i x dF) :
    partialDeriv (fun y => (B y • field y) i) i x =
      dB * field x i + B x * dF := by
  have hprod : HasPartialAt (fun y => B y * field y i) i x
      (dB * field x i + B x * dF) := hB.mul hF
  have heq : (fun y => (B y • field y) i) = (fun y => B y * field y i) := by
    funext y
    rfl
  rw [heq]
  exact hprod.partial_eq

/-- Pointwise derivative data sufficient to evaluate the divergence of `B f`. -/
structure DulacDerivativeData (B : Phase2 → ℝ) (field : Phase2 → Phase2) (x : Phase2) where
  dB0 : ℝ
  dB1 : ℝ
  dF00 : ℝ
  dF11 : ℝ
  hB0 : HasPartialAt B 0 x dB0
  hB1 : HasPartialAt B 1 x dB1
  hF00 : HasPartialAt (fun y => field y 0) 0 x dF00
  hF11 : HasPartialAt (fun y => field y 1) 1 x dF11

/-- Exact divergence formula for a Dulac-scaled planar field from certified coordinate derivatives. -/
theorem divergence_scaled_eq
    {B : Phase2 → ℝ} {field : Phase2 → Phase2} {x : Phase2}
    (D : DulacDerivativeData B field x) :
    divergence (fun y => B y • field y) x =
      (D.dB0 * field x 0 + B x * D.dF00) +
      (D.dB1 * field x 1 + B x * D.dF11) := by
  unfold divergence
  rw [partial_scaled_component D.hB0 D.hF00]
  rw [partial_scaled_component D.hB1 D.hF11]

/-- A certificate-friendly sufficient condition for the positive-sign branch of Bendixson--Dulac. -/
theorem strictOneSignOn_of_divergence_scaled_pos
    {B : Phase2 → ℝ} {field : Phase2 → Phase2} {region : Set Phase2}
    (h : ∀ x ∈ region, 0 < divergence (fun y => B y • field y) x) :
    StrictOneSignOn (divergence (fun y => B y • field y)) region :=
  Or.inl h

/-- A certificate-friendly sufficient condition for the negative-sign branch of Bendixson--Dulac. -/
theorem strictOneSignOn_of_divergence_scaled_neg
    {B : Phase2 → ℝ} {field : Phase2 → Phase2} {region : Set Phase2}
    (h : ∀ x ∈ region, divergence (fun y => B y • field y) x < 0) :
    StrictOneSignOn (divergence (fun y => B y • field y)) region :=
  Or.inr h


/-! ## Boundary flux along an exact periodic trajectory -/

/-- The oriented planar flux density `G · n ds` written against a tangent vector `v=(dx,dy)`:
`G₀ dy - G₁ dx`.  This is the boundary integrand appearing in Green's divergence theorem. -/
def boundaryFluxDensity (G v : Phase2) : ℝ :=
  G 0 * v 1 - G 1 * v 0

/-- A scalar multiple of a vector has zero oriented flux across that same vector.  This is the
pointwise algebra behind Bendixson--Dulac: along an ODE trajectory the tangent is `f`, while the
scaled field is `B f`, so the boundary flux vanishes identically. -/
@[simp] theorem boundaryFluxDensity_smul_self (B : ℝ) (v : Phase2) :
    boundaryFluxDensity (B • v) v = 0 := by
  simp [boundaryFluxDensity, Pi.smul_apply, smul_eq_mul]
  ring

/-- Pointwise zero-flux identity along any exact planar ODE solution.  No Green theorem is used here;
this is purely the fact that the vector field is tangent to its own trajectory. -/
theorem dulac_scaled_flux_density_zero
    {B : Phase2 → ℝ} {field : Phase2 → Phase2}
    (γ : ℝ → Phase2) (hsol : IsSolution field γ) (t : ℝ) :
    boundaryFluxDensity (B (γ t) • field (γ t)) (field (γ t)) = 0 := by
  exact boundaryFluxDensity_smul_self (B (γ t)) (field (γ t))

/-- Specialization of the zero-flux identity to an exact periodic trajectory. -/
theorem PeriodicTrajectory.dulac_scaled_flux_density_zero
    {B : Phase2 → ℝ} {field : Phase2 → Phase2}
    (P : PeriodicTrajectory field) (t : ℝ) :
    boundaryFluxDensity (B (P.orbit t) • field (P.orbit t)) (field (P.orbit t)) = 0 := by
  exact boundaryFluxDensity_smul_self (B (P.orbit t)) (field (P.orbit t))

/-! ## Reduction to the genuine Green/Jordan kernel -/

/-- The genuinely geometric-analytic kernel after period normalization and ODE uniqueness have been
removed: a **simple closed** periodic orbit lying inside a Dulac region with strict one-sign
scaled divergence is impossible.

A proof of this proposition needs only the Jordan interior construction and Green's divergence
theorem for that interior.  It no longer has to prove that the periodic parametrization is simple. -/
def GreenJordanSimpleCycleKernelTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field),
    P.SimpleClosedCycle → Set.range P.orbit ⊆ D.region → False

/-- For a locally Lipschitz planar field, the simple-cycle Green/Jordan kernel excludes every
nonconstant periodic trajectory in the Dulac region.  The input trajectory is automatically
replaced by its least-period simple representative with the same geometric image. -/
theorem noPeriodicTrajectoryInRegion_of_simpleGreenJordanKernel
    (hGJ : GreenJordanSimpleCycleKernelTarget)
    {field : Phase2 → Phase2} (D : BendixsonDulacData field)
    (hlip : LocallyLipschitz field)
    (P : PeriodicTrajectory field)
    (hinside : Set.range P.orbit ⊆ D.region) : False := by
  let Q := P.leastPeriodRepresentative
  have hsimple : Q.SimpleClosedCycle :=
    P.leastPeriodRepresentative_simpleClosedCycle hlip
  have hsame : Set.range Q.orbit = Set.range P.orbit := by
    rfl
  apply hGJ field D Q hsimple
  simpa [hsame] using hinside

/-- The remaining Green/Jordan kernel for Bendixson--Dulac, after the local differential calculus
and zero boundary-flux calculation have been discharged.  A future proof only has to turn a simple
periodic orbit into its Jordan interior and identify the boundary flux with the area integral of
`div(B f)`; strict one-sign divergence then contradicts the zero-flux theorem above. -/
def GreenJordanDulacKernelTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field),
    Set.range P.orbit ⊆ D.region → False

/-- The Green/Jordan kernel immediately supplies the public Bendixson--Dulac target. -/
theorem bendixsonDulacTarget_of_greenJordanKernel
    (h : GreenJordanDulacKernelTarget) : BendixsonDulacTarget := by
  intro field D hopen hconv hfield hB P hinside
  let D' : BendixsonDulacData field :=
    { region := D.region
      dulac := D.dulac
      oneSign := D.oneSign
      open_region := hopen
      convex_region := hconv
      smooth_field := hfield
      smooth_dulac := hB }
  exact h field D' P hinside

end Planar

end CRNT
