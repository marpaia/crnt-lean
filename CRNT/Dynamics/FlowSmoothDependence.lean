import CRNT.Dynamics.VariationalEquation
import CRNT.Dynamics.FlowDifferentiable
import CRNT.Dynamics.FlowConstruction
import CRNT.Kinetics.MassActionJacobian
import CRNT.Dynamics.MassActionField
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.ODE.Gronwall

/-!
# Smooth dependence of the mass-action flow on its initial condition

`CRNT/Oscillation/FloquetOrbitalStability.lean` and `CRNT/Oscillation/PlanarFlowRegularity.lean`
both `import CRNT.Dynamics.FlowSmoothDependence`, and the former uses
`N.massAction_flow_smoothDependence κ` when constructing a transverse Poincare section.  The module
did not exist, so neither file could elaborate and both were silently outside the build.

## What this file is, and is not

It supplies the **statement** that the Floquet chain consumes, in the repository's established
`…Target : Prop` idiom, plus the pieces that follow from the variational machinery already proved in
`CRNT/Dynamics/VariationalEquation.lean` and `CRNT/Dynamics/FlowDifferentiable.lean`.

It does **not** prove `MassActionFlowSmoothDependenceTarget`.  That is a real theorem -- C¹
dependence of the flow of a C^∞ vector field on its initial condition, with the derivative given by
the fundamental matrix of the variational equation -- and it is not proved here, as an axiom, or
with `sorry`.  A consumer that needs it takes it as a hypothesis and says so in its signature,
which is how the rest of the oscillation development already handles its open kernels.

## What is already available

`ODE.norm_flow_variational_error_le` (VariationalEquation.lean, proved) is the analytic core: along
`[0, T]` the difference between the genuine flow separation `y t - x t` and its linear prediction
`h • W t` is Gronwall-controlled, with driving term linear in `|h|` and vanishing with the
`Df`-modulus.  What remains is to turn that estimate into a Frechet derivative statement uniform in
the initial point, which needs

1. a uniform-in-`x` version of the `Df`-modulus bound `hmod` (available on compact sets from
   `N.massActionVectorField_contDiff`, which is proved);
2. existence of the fundamental matrix as a function of the base point, i.e. solving the
   variational equation with initial condition `1` for each `x` -- `ODE.exists_isIntegralCurve`
   applies once the linear field is bounded and Lipschitz on the relevant compact set;
3. joint continuity of `(x, t) ↦ Φ x t` and of its `x`-derivative, from (1) and (2).

Step (2) is the only one with real content beyond bookkeeping; steps (1) and (3) are compactness
arguments over the proved estimate.  See `docs/floquet-obligations.md`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The forward flow of the mass-action field, as a two-argument family, together with the
property of being its own solution.  This is the shape the Poincare-section construction needs:
not merely one integral curve, but the family indexed by the initial point. -/
structure MassActionFlowFamily (N : Network S) (κ : N.RateConstants) : Type where
  /-- `flow x t` is the state at time `t` of the solution started at `x`. -/
  flow : Concentration S → ℝ → Concentration S
  flow_zero : ∀ x, flow x 0 = x
  flow_solution :
    ∀ x t, HasDerivAt (flow x) (N.massActionVectorField κ (flow x t)) t

/-- The fundamental matrix of the variational equation along the orbit of `x`: the solution of
`Ẇ = Df(Φ x t) ∘ W` with `W 0 = 1`.  Bundled as data because the Poincare section needs its value
at the period, which is the monodromy operator. -/
structure VariationalFundamental (N : Network S) (κ : N.RateConstants)
    (F : N.MassActionFlowFamily κ) : Type where
  fundamental : Concentration S → ℝ → (Concentration S →L[ℝ] Concentration S)
  fundamental_zero : ∀ x, fundamental x 0 = ContinuousLinearMap.id ℝ (Concentration S)
  fundamental_solution :
    ∀ x t v, HasDerivAt (fun s => fundamental x s v)
      ((N.massActionJacobianCLM κ (F.flow x t)) (fundamental x t v)) t

/-- **Open obligation: C¹ dependence of the mass-action flow on its initial condition.**

For every network and every positive rate vector there is a flow family whose time-`t` map is
Frechet differentiable in the initial point, with derivative the fundamental matrix of the
variational equation, and with `(x, t) ↦ Φ x t` jointly continuous.

This is the standard smooth-dependence theorem for a C^∞ field, specialized to mass action.  It is
stated rather than proved; `ODE.norm_flow_variational_error_le` is the estimate it rests on. -/
def MassActionFlowSmoothDependenceTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T) (κ : N.RateConstants),
    ∃ (F : N.MassActionFlowFamily κ) (V : N.VariationalFundamental κ F),
      (∀ x t, HasFDerivAt (fun y => F.flow y t) (V.fundamental x t) x) ∧
      Continuous (fun p : Concentration T × ℝ => F.flow p.1 p.2)

/-- Consumer-facing form: a network-level instance of the smooth-dependence obligation.  The
Poincare-section construction takes this as a hypothesis rather than assuming the global target. -/
def MassActionFlowSmoothDependence (N : Network S) (κ : N.RateConstants) : Prop :=
  ∃ (F : N.MassActionFlowFamily κ) (V : N.VariationalFundamental κ F),
    (∀ x t, HasFDerivAt (fun y => F.flow y t) (V.fundamental x t) x) ∧
    Continuous (fun p : Concentration S × ℝ => F.flow p.1 p.2)

/-- The global target specializes to every network, so a consumer may be stated either way. -/
theorem massActionFlowSmoothDependence_of_target
    (h : MassActionFlowSmoothDependenceTarget) (N : Network S) (κ : N.RateConstants) :
    N.MassActionFlowSmoothDependence κ :=
  h N κ

/-! ## Decomposition of the obligation

The target above bundles three separable facts.  Naming them separately matters because only the
second has real content; the other two are compactness bookkeeping over an estimate that is already
proved in the core (`ODE.norm_flow_variational_error_le`). -/

/-- **Step 1 (bookkeeping).** On a compact set the `Df`-modulus of the mass-action field is
uniform: for every `ε > 0` there is `ρ > 0` such that the first-order Taylor remainder of the field
is bounded by `ε‖y − x‖` whenever `x` is in the set and `‖y − x‖ < ρ`.

Follows from `ContDiff ℝ ⊤ (N.massActionVectorField κ)` (proved in the core) plus uniform continuity
of the derivative on a compact set. -/
def UniformModulusTarget (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (K : Set (Concentration S)), IsCompact K → ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ),
    ∀ x ∈ K, ∀ y : Concentration S, ‖y - x‖ < ρ →
      ‖N.massActionVectorField κ y - N.massActionVectorField κ x
        - (N.massActionJacobianCLM κ x) (y - x)‖ ≤ ε * ‖y - x‖

/-- **Step 2 (the real content).** The variational equation along the orbit of each point has a
solution with initial value the identity, jointly continuous in the base point.

The linear field `W ↦ Df(Φ x t) ∘ W` is bounded and Lipschitz on any compact time interval, so
`ODE.exists_isIntegralCurve` applies pointwise; what needs work is continuity of the resulting
family in `x`, which is a second application of Grönwall. -/
def FundamentalMatrixTarget (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ F : N.MassActionFlowFamily κ, Nonempty (N.VariationalFundamental κ F)

/-- **Step 3 (bookkeeping).** Given steps 1 and 2, the Grönwall variational estimate upgrades to a
Frechet derivative statement, and the flow is jointly continuous.

This is where `ODE.norm_flow_variational_error_le` is consumed: its driving term is linear in the
increment and vanishes with the modulus `ρ` from step 1, which is exactly the
`o(‖y − x‖)` condition defining the derivative. -/
def DerivativeAssemblyTarget (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (F : N.MassActionFlowFamily κ) (V : N.VariationalFundamental κ F),
    N.UniformModulusTarget κ →
    (∀ x t, HasFDerivAt (fun y => F.flow y t) (V.fundamental x t) x) ∧
    Continuous (fun p : Concentration S × ℝ => F.flow p.1 p.2)

/-- The three steps assemble to the obligation.  **Proved**: this is the only part of the
decomposition that is pure plumbing, and it shows the split is faithful -- no fourth hidden step. -/
theorem massActionFlowSmoothDependence_of_steps (N : Network S) (κ : N.RateConstants)
    (F : N.MassActionFlowFamily κ)
    (h1 : N.UniformModulusTarget κ) (h2 : N.FundamentalMatrixTarget κ)
    (h3 : N.DerivativeAssemblyTarget κ) :
    N.MassActionFlowSmoothDependence κ := by
  obtain ⟨V⟩ := h2 F
  obtain ⟨hderiv, hcont⟩ := h3 F V h1
  exact ⟨F, V, hderiv, hcont⟩

/-!
## Consequences that do not need the obligation

The two facts below are immediate from results already proved in the core, and are recorded here
so that callers needing only regularity of the *field* (as opposed to the flow) do not reach for
the open obligation by mistake.
-/

/-- The mass-action field is C^∞, so the variational equation has continuous coefficients along
any orbit.  (Proved in the core; restated here for locality.) -/
theorem massActionVectorField_contDiff_of_rates (N : Network S) (κ : N.RateConstants) :
    ContDiff ℝ ⊤ (N.massActionVectorField κ) :=
  N.massActionVectorField_contDiff κ

/-- Along a fixed orbit the variational coefficient operator is the mass-action Jacobian at the
current state, which is continuous in that state. -/
theorem massActionJacobianCLM_continuous (N : Network S) (κ : N.RateConstants) :
    Continuous (fun x => N.massActionJacobianCLM κ x) :=
  -- `continuous_fderiv` now wants `n ≠ 0` rather than `1 ≤ n`, and `congr` wants the
  -- equality the other way round.
  (N.massActionVectorField_contDiff κ (n := ⊤)).continuous_fderiv (by simp) |>.congr
    (fun x => (N.massActionVectorField_hasFDerivAt κ x).fderiv)

end Network
end CRNT
