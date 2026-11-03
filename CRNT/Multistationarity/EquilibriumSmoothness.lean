import CRNT.Multistationarity.DegreeExistence
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Multistationarity.DegreeStability
import CRNT.Multistationarity.LocalDegreeOn
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# The equilibrium of a CRN depends smoothly (in fact analytically) on the rate constants

## The mathematical statement

Let `N` be a chemical reaction network, `κ` a vector of rate constants, `x₀` a point of a
compatibility class, and let `G_κ` be the **reduced field** of `N` on that class: in the chart
coordinates of the class,

`G_κ y = stoichProj (F_κ (x₀ + stoichChart y))`,

where `F_κ` is the mass-action field.  The zeros of `G_κ` are exactly the mass-action steady
states of the class.

The classical fact — used in every numerical study of CRNT, and the analytic backbone of the
"parameter regions for multistationarity" of Conradi–Feliu–Mincheva–Wiuf and of Craciun's
*Chemical Reaction Network Theory* — is:

> **Local analytic dependence.**  If `y*` is a *nondegenerate* zero of `G_κ` (that is, the
> reduced Jacobian `DG_κ (y*)` is invertible), then there is a neighbourhood `U` of `κ` and a
> uniquely determined equilibrium `y(κ')` for every `κ' ∈ U`, and `κ ↦ y(κ)` is
> **real-analytic** on `U`.

This module formalizes that statement, together with the local constancy of the *local degree*
of the steady-state map in the rate constants, and a worked instance (the reversible pair
`A ⇌ B`, whose equilibrium is a *rational* function of the rates).

## What the repository already contained

* the **tropical** implicit function theorem (`CRNT.Algebra.TropicalLifting`): the leading
  system of a tropical equilibration with injective Jacobian lifts to a root of the full
  system for small `ε`, with a continuous lift.  This is the *tropical* analogue of the
  statement formalized here, which is the *classical* (analytic) one;
* the **degree machinery**: the local degree of a map at a nondegenerate preimage point is
  locally constant in the *value* (`CRNT.Multistationarity.DegreeStability`), the relative
  local degree `localDegreeOn` (`CRNT.Multistationarity.LocalDegreeOn`), and the class degree
  of the steady-state map (`CRNT.Multistationarity.DegreeExistence`);
* the **affine dependence of the field on the rates**: `massActionVectorField_interpolate`
  (`CRNT.Multistationarity.DegreeExistence`) proves that the mass-action field is *linear* in
  the rate constants, `steadyStateMap_interpolate` transports this to the reduced field, and
  `steadyStateMap_contDiff` records the `C^∞`-smoothness of the reduced field in the class
  coordinates.

## What this module adds

* `massActionVectorFieldAtRate`, `massActionJacobianCLMAtRate`, `reducedFieldAtRate`,
  `reducedJacobianCLMAtRate`: the field, its Jacobian, the reduced field and the reduced
  Jacobian at an **arbitrary real rate vector** `ρ : N.R → ℝ` (positivity of the rates is *not*
  required), together with their agreement with the repository's notions at positive rate
  constants, and the affinity of the field in the rates
  (`massActionVectorFieldAtRate_add`, `reducedFieldAtRate_add`);
* `reducedFieldAtRate_joint_contDiff`: the reduced field is **jointly** `C^∞` in the rate
  vector and the class coordinates — the analytic input of the implicit function theorem;
* `equilibrium_smooth_of_nonSingular`: the **implicit function theorem for the equilibrium**;
  near a nondegenerate equilibrium the equilibrium is a `C¹` function of the rate constants;
* `reducedFieldOrientationSign_eventually_eq_of_nonSingular`: the **local degree of the
  steady-state map is locally constant in the rate constants**;
* `reducedJacobianCLM_eq_smul_id`, `reducedJacobianCLMAtRate_eq_smul_id`: the **nondegeneracy
  criterion in the class** — the reduced Jacobian is the ambient Jacobian restricted to the
  stoichiometric subspace;
* `RevPair`: a **worked instance** — the reversible pair `A ⇌ B`, whose equilibrium in the
  class of total concentration `c` is `x_A = c k_r/(k_f + k_r)`, `x_B = c k_f/(k_f + k_r)`, a
  rational (hence real-analytic) function of the rates, and whose reduced Jacobian is
  `-(k_f + k_r)` times the identity.

## What is *not* claimed

* **No global description of the multistationarity region.**  This module proves the local
  statement only: the local degree of the steady-state map cannot change near a nondegenerate
  equilibrium as the rates vary.  It does **not** describe the set of rate vectors for which
  the class carries several positive steady states; that is leaf M13 of the field map
  (`CRNT.Multistationarity.MultistationarityRegion`), and the global topological arguments of
  Craciun–Feinberg are not formalized here.
* **No global description of the equilibrium branch.**  The equilibrium `ψ` produced by
  `equilibrium_smooth_of_nonSingular` is defined only locally, near the given equilibrium; no
  continuation along a path of rate vectors is provided.
* The *analytic* (`AnalyticAt`) version of the implicit function theorem is not stated for the
  equilibrium branch; the `C¹` version is.  The field is a polynomial in the rate constants,
  so the branch is in fact real-analytic; the analytic statement is given for the reversible
  pair in `RevPair.equilibrium_component_analyticAt`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The rate vector of a rate-constant assignment. -/
def rateVector (N : Network S) (κ : N.RateConstants) : N.R → ℝ := κ.k

/-- The mass-action vector field at an arbitrary real rate vector (positivity not required). -/
noncomputable def massActionVectorFieldAtRate (N : Network S) (ρ : N.R → ℝ)
    (x : Concentration S) : Concentration S :=
  fun s => ∑ r : N.R, (ρ r * (N.reaction r).source.massActionMonomial x) * N.reactionVector r s

theorem massActionVectorFieldAtRate_eq (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    N.massActionVectorFieldAtRate κ.k x = N.massActionVectorField κ x := by
  funext s
  simp only [massActionVectorFieldAtRate, massActionVectorField_apply, massActionRate]

/-- The mass-action Jacobian at an arbitrary real rate vector. -/
noncomputable def massActionJacobianCLMAtRate (N : Network S) (ρ : N.R → ℝ)
    (x : Concentration S) : Concentration S →L[ℝ] Concentration S :=
  ∑ r : N.R, (ρ r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight (N.reactionVector r)

theorem massActionJacobianCLMAtRate_eq (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    N.massActionJacobianCLMAtRate κ.k x = N.massActionJacobianCLM κ x := by
  simp only [massActionJacobianCLMAtRate, massActionJacobianCLM]

omit [DecidableEq S] in
/-- The source monomial of a reaction is `C^∞` in the concentrations. -/
theorem massActionMonomial_contDiff (y : Complex S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : Concentration S => y.massActionMonomial x) := by
  show ContDiff ℝ n (fun x : Concentration S => ∏ s', x s' ^ y s')
  exact contDiff_prod fun s' _ => (contDiff_apply ℝ ℝ s').pow _

/-- The mass-action field at a fixed rate vector is `C^∞` in the concentrations. -/
theorem massActionVectorFieldAtRate_contDiff (N : Network S) (ρ : N.R → ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun x => N.massActionVectorFieldAtRate ρ x) := by
  rw [contDiff_pi]
  intro s
  simp only [massActionVectorFieldAtRate]
  refine ContDiff.sum fun r _ => ?_
  show ContDiff ℝ n (fun x : Concentration S =>
    (ρ r * (N.reaction r).source.massActionMonomial x) * N.reactionVector r s)
  refine ContDiff.mul ?_ contDiff_const
  refine contDiff_const.mul ?_
  exact (massActionMonomial_contDiff (N.reaction r).source)

/-- **The mass-action field is jointly `C^∞` in the rate vector and the concentrations.** -/
theorem massActionVectorFieldAtRate_joint_contDiff (N : Network S)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : (N.R → ℝ) × Concentration S => N.massActionVectorFieldAtRate p.1 p.2) := by
  rw [contDiff_pi]
  intro s
  simp only [massActionVectorFieldAtRate]
  refine ContDiff.sum fun r _ => ?_
  show ContDiff ℝ n (fun p : (N.R → ℝ) × Concentration S =>
    (p.1 r * (N.reaction r).source.massActionMonomial p.2) * N.reactionVector r s)
  refine ContDiff.mul ?_ contDiff_const
  refine ContDiff.mul ?_ ?_
  · have h : (fun p : (N.R → ℝ) × Concentration S => p.1 r)
      = fun p : (N.R → ℝ) × Concentration S =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N.R => ℝ) r) (p.1) := by
      funext p; simp [ContinuousLinearMap.proj_apply]
    rw [h]
    show ContDiff ℝ n (fun p : (N.R → ℝ) × Concentration S =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N.R => ℝ) r) (p.1))
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N.R => ℝ) r).contDiff.comp contDiff_fst
  · have hmono : ContDiff ℝ n (fun x : Concentration S =>
        (N.reaction r).source.massActionMonomial x) :=
      (massActionMonomial_contDiff (N.reaction r).source)
    show ContDiff ℝ n (fun p : (N.R → ℝ) × Concentration S =>
      (N.reaction r).source.massActionMonomial p.2)
    exact hmono.comp contDiff_snd

/-- **The mass-action field at a rate vector has the mass-action Jacobian as its derivative.** -/
theorem massActionVectorFieldAtRate_hasFDerivAt (N : Network S) (ρ : N.R → ℝ)
    (x : Concentration S) :
    HasFDerivAt (fun x => N.massActionVectorFieldAtRate ρ x)
      (N.massActionJacobianCLMAtRate ρ x) x := by
  have hfun : (fun x : Concentration S => N.massActionVectorFieldAtRate ρ x)
      = ∑ r : N.R,
        (fun x => (ρ r * (N.reaction r).source.massActionMonomial x) • N.reactionVector r) := by
    funext x s
    simp only [massActionVectorFieldAtRate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hr : ∀ r : N.R,
      HasFDerivAt (fun x : Concentration S =>
          (ρ r * (N.reaction r).source.massActionMonomial x) • N.reactionVector r)
        ((ρ r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight
            (N.reactionVector r)) x := by
    intro r
    exact ((massActionMonomial_hasFDerivAt (N.reaction r).source x).const_mul (ρ r)).smul_const
      (N.reactionVector r)
  rw [hfun]
  exact HasFDerivAt.sum fun r _ => hr r

/-- **The reduced field at a rate vector.**  This is the mass-action field restricted to the
compatibility class of `x₀` and read in the chart coordinates, at an arbitrary real rate vector
(positivity of the rates is not required). -/
noncomputable def reducedFieldAtRate (N : Network S) (ρ : N.R → ℝ) (x₀ : Concentration S) :
    (Fin N.stoichRank → ℝ) → (Fin N.stoichRank → ℝ) :=
  fun y => N.stoichProj (N.massActionVectorFieldAtRate ρ (N.affineChart x₀ y))

/-- The reduced field at a rate vector agrees with the reduced field at the corresponding
positive rate constants. -/
theorem reducedFieldAtRate_eq (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    N.reducedFieldAtRate κ.k x₀ y = N.reducedField κ x₀ y := by
  simp only [reducedFieldAtRate, reducedField, massActionVectorFieldAtRate_eq]

/-- **The reduced Jacobian at a rate vector.** -/
noncomputable def reducedJacobianCLMAtRate (N : Network S) (ρ : N.R → ℝ) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) : (Fin N.stoichRank → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ) :=
  N.stoichProj.comp ((N.massActionJacobianCLMAtRate ρ (N.affineChart x₀ y)).comp N.stoichChart)

theorem reducedJacobianCLMAtRate_eq (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    N.reducedJacobianCLMAtRate κ.k x₀ y = N.reducedJacobianCLM κ x₀ y := by
  simp only [reducedJacobianCLMAtRate, reducedJacobianCLM, massActionJacobianCLMAtRate_eq]

/-- **The reduced field at a rate vector is `C¹`, with the reduced Jacobian as derivative.** -/
theorem reducedFieldAtRate_hasFDerivAt (N : Network S) (ρ : N.R → ℝ) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    HasFDerivAt (fun y => N.reducedFieldAtRate ρ x₀ y) (N.reducedJacobianCLMAtRate ρ x₀ y) y := by
  have h1 : HasFDerivAt (N.affineChart x₀) N.stoichChart y := N.affineChart_hasFDerivAt x₀ y
  have h2 : HasFDerivAt (fun x => N.massActionVectorFieldAtRate ρ x)
      (N.massActionJacobianCLMAtRate ρ (N.affineChart x₀ y)) (N.affineChart x₀ y) :=
    N.massActionVectorFieldAtRate_hasFDerivAt ρ (N.affineChart x₀ y)
  have h3 : HasFDerivAt (fun y => N.massActionVectorFieldAtRate ρ (N.affineChart x₀ y))
      ((N.massActionJacobianCLMAtRate ρ (N.affineChart x₀ y)).comp N.stoichChart) y :=
    h2.comp y h1
  exact N.stoichProj.hasFDerivAt.comp y h3

/-- The reduced field at a fixed rate vector is `C^∞` in the class coordinates. -/
theorem reducedFieldAtRate_contDiff (N : Network S) (ρ : N.R → ℝ) (x₀ : Concentration S)
    {n : WithTop ℕ∞} : ContDiff ℝ n (fun y => N.reducedFieldAtRate ρ x₀ y) := by
  change ContDiff ℝ n (fun y => N.stoichProj (N.massActionVectorFieldAtRate ρ (N.affineChart x₀ y)))
  have hchart : ContDiff ℝ n (N.affineChart x₀) :=
    contDiff_const.add N.stoichChart.contDiff
  have hf : ContDiff ℝ n (fun x => N.massActionVectorFieldAtRate ρ x) :=
    N.massActionVectorFieldAtRate_contDiff ρ
  exact N.stoichProj.contDiff.comp (hf.comp hchart)

/-- **The mass-action field, composed with the affine chart, is jointly `C^∞` in the rate
vector and the class coordinates.** -/
theorem massActionVectorFieldAtRate_chart_joint_contDiff (N : Network S) (x₀ : Concentration S)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
      N.massActionVectorFieldAtRate p.1 (N.affineChart x₀ p.2)) := by
  rw [contDiff_pi]
  intro s
  simp only [massActionVectorFieldAtRate]
  refine ContDiff.sum fun r _ => ?_
  show ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
    (p.1 r * (N.reaction r).source.massActionMonomial (N.affineChart x₀ p.2))
      * N.reactionVector r s)
  refine ContDiff.mul ?_ contDiff_const
  refine ContDiff.mul ?_ ?_
  · have h : (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) => p.1 r)
      = fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N.R => ℝ) r) (p.1) := by
      funext p; simp [ContinuousLinearMap.proj_apply]
    rw [h]
    show ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N.R => ℝ) r) (p.1))
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N.R => ℝ) r).contDiff.comp contDiff_fst
  · have hmono : ContDiff ℝ n (fun x : Concentration S =>
        (N.reaction r).source.massActionMonomial x) :=
      (massActionMonomial_contDiff (N.reaction r).source)
    have hchart : ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
        N.affineChart x₀ p.2) :=
      contDiff_const.add (N.stoichChart.contDiff.comp contDiff_snd)
    show ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
      (N.reaction r).source.massActionMonomial (N.affineChart x₀ p.2))
    exact hmono.comp hchart

/-- **The reduced field is jointly `C^∞` in the rate vector and the class coordinates.** -/
theorem reducedFieldAtRate_joint_contDiff (N : Network S) (x₀ : Concentration S)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
      N.reducedFieldAtRate p.1 x₀ p.2) := by
  change ContDiff ℝ n (fun p : (N.R → ℝ) × (Fin N.stoichRank → ℝ) =>
    N.stoichProj (N.massActionVectorFieldAtRate p.1 (N.affineChart x₀ p.2)))
  exact N.stoichProj.contDiff.comp (N.massActionVectorFieldAtRate_chart_joint_contDiff x₀)

/-- **The joint reduced field**, as a function of the rate vector and the class coordinates. -/
noncomputable def reducedFieldJoint (N : Network S) (x₀ : Concentration S) :
    ((N.R → ℝ) × (Fin N.stoichRank → ℝ)) → (Fin N.stoichRank → ℝ) :=
  fun p => N.reducedFieldAtRate p.1 x₀ p.2

theorem reducedFieldJoint_contDiff (N : Network S) (x₀ : Concentration S) :
    ContDiff ℝ 1 (N.reducedFieldJoint x₀) := by
  exact N.reducedFieldAtRate_joint_contDiff x₀

/-- **The class-coordinate part of the joint derivative of the reduced field is the reduced
Jacobian.**  This is the analytic input of the implicit function theorem. -/
theorem fderiv_reducedFieldJoint_inr (N : Network S) (x₀ : Concentration S) (ρ : N.R → ℝ)
    (y : Fin N.stoichRank → ℝ) :
    fderiv ℝ (N.reducedFieldJoint x₀) (ρ, y)
      ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)
      = N.reducedJacobianCLMAtRate ρ x₀ y := by
  have hcd : ContDiffAt ℝ 1 (N.reducedFieldJoint x₀) (ρ, y) :=
    (N.reducedFieldJoint_contDiff x₀).contDiffAt
  have hJ : HasFDerivAt (N.reducedFieldJoint x₀)
      (fderiv ℝ (N.reducedFieldJoint x₀) (ρ, y)) (ρ, y) :=
    (hcd.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hι : HasFDerivAt (fun z : Fin N.stoichRank → ℝ => (ρ, z))
      (ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)) y :=
    hasFDerivAt_prodMk_right ρ y
  have hcomp : HasFDerivAt (fun z : Fin N.stoichRank → ℝ =>
      N.reducedFieldAtRate ρ x₀ z)
      ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ, y))
        ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)) y :=
    hJ.comp y hι
  have hG : HasFDerivAt (fun z : Fin N.stoichRank → ℝ => N.reducedFieldAtRate ρ x₀ z)
      (N.reducedJacobianCLMAtRate ρ x₀ y) y :=
    N.reducedFieldAtRate_hasFDerivAt ρ x₀ y
  exact hcomp.unique hG

/-- **The equilibrium is a smooth function of the rate constants near a nondegenerate
equilibrium.**  Let `ρ` be a rate vector and `y` a zero of the reduced field of `ρ` at the class
of `x₀`.  If the reduced Jacobian at `y` is invertible — the classical *nondegeneracy*
condition — then near `ρ` there is a uniquely determined equilibrium `ψ ρ'` of the reduced field
of `ρ'`, it satisfies `ψ ρ = y`, and `ψ` is `C¹` in the rate constants.

This is the local analytic dependence of a CRN equilibrium on the rate constants; it is the
analytic backbone of the "parameter regions for multistationarity" of Conradi–Feliu–Mincheva–Wiuf
and of every numerical study of CRNT. -/
theorem equilibrium_smooth_of_nonSingular (N : Network S) (x₀ : Concentration S)
    (ρ : N.R → ℝ) (y : Fin N.stoichRank → ℝ)
    (hy : N.reducedFieldAtRate ρ x₀ y = 0)
    (hns : (N.reducedJacobianCLMAtRate ρ x₀ y).IsInvertible) :
    ∃ ψ : (N.R → ℝ) → (Fin N.stoichRank → ℝ),
      ψ ρ = y ∧ ContDiffAt ℝ 1 ψ ρ ∧
      (∀ᶠ ρ' in 𝓝 ρ, N.reducedFieldAtRate ρ' x₀ (ψ ρ') = 0) := by
  have hcd : ContDiffAt ℝ 1 (N.reducedFieldJoint x₀) (ρ, y) :=
    (N.reducedFieldJoint_contDiff x₀).contDiffAt
  have hinr : fderiv ℝ (N.reducedFieldJoint x₀) (ρ, y)
      ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)
      = N.reducedJacobianCLMAtRate ρ x₀ y :=
    N.fderiv_reducedFieldJoint_inr x₀ ρ y
  have hinv : (fderiv ℝ (N.reducedFieldJoint x₀) (ρ, y)
      ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).IsInvertible := by
    rw [hinr]
    exact hns
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  refine ⟨ψ, hcd.implicitFunction_apply_self one_ne_zero hinv,
    hcd.contDiffAt_implicitFunction one_ne_zero hinv, ?_⟩
  filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with ρ' hρ'
  rw [← hψdef] at hρ'
  have h2 : N.reducedFieldAtRate ρ' x₀ (ψ ρ') = N.reducedFieldAtRate ρ x₀ y := by
    simpa only [reducedFieldJoint] using hρ'
  rw [h2, hy]

/-- **The orientation sign of the reduced field at a point.**  This is the local degree of the
steady-state map at a nondegenerate equilibrium: the signed count of the solutions of the
reduced field near a nondegenerate zero. -/
noncomputable def reducedFieldOrientationSign (N : Network S) (ρ : N.R → ℝ) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) : ℤ :=
  ((SignType.sign (LinearMap.det (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap) : SignType) : ℤ)

/-- The orientation sign is `±1`, and it is nonzero exactly when the reduced Jacobian is
invertible. -/
theorem reducedFieldOrientationSign_ne_zero_of_isInvertible (N : Network S) (ρ : N.R → ℝ)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    (hns : (N.reducedJacobianCLMAtRate ρ x₀ y).IsInvertible) :
    N.reducedFieldOrientationSign ρ x₀ y ≠ 0 := by
  have hdet : LinearMap.det (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap ≠ 0 := by
    by_contra hcon
    have h1 : LinearMap.ker (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap ≠ ⊥ := by
      rw [← LinearMap.det_eq_zero_iff_ker_ne_bot]
      exact hcon
    have h2 : LinearMap.ker (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr hns.injective
    exact h1 h2
  unfold reducedFieldOrientationSign
  rcases lt_trichotomy
      (LinearMap.det (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap) 0 with h | h | h
  · rw [sign_neg h]
    norm_num
  · exact absurd h hdet
  · rw [sign_pos h]
    norm_num

/-- **The local degree of the steady-state map is locally constant in the rate constants.**
Let `ρ` be a rate vector and `y` a nondegenerate zero of the reduced field of `ρ` in the class of
`x₀`.  Then near `ρ` the equilibria `ψ ρ'` form a smooth branch, and the orientation sign — the
local degree of the steady-state map at the equilibrium — is *constant* on that branch.  This is
the analytic reason why the multistationarity region of the rate constants has a non-empty
interior: the local degree cannot change without a degeneracy. -/
theorem reducedFieldOrientationSign_eventually_eq_of_nonSingular (N : Network S) (x₀ : Concentration S)
    (ρ : N.R → ℝ) (y : Fin N.stoichRank → ℝ)
    (hy : N.reducedFieldAtRate ρ x₀ y = 0)
    (hns : (N.reducedJacobianCLMAtRate ρ x₀ y).IsInvertible) :
    ∃ ψ : (N.R → ℝ) → (Fin N.stoichRank → ℝ), ψ ρ = y ∧
      (∀ᶠ ρ' in 𝓝 ρ, N.reducedFieldAtRate ρ' x₀ (ψ ρ') = 0) ∧
      ∀ᶠ ρ' in 𝓝 ρ,
        N.reducedFieldOrientationSign ρ' x₀ (ψ ρ')
          = N.reducedFieldOrientationSign ρ x₀ y := by
  obtain ⟨ψ, hψ0, hψcd, hψzero⟩ :=
    N.equilibrium_smooth_of_nonSingular x₀ ρ y hy hns
  refine ⟨ψ, hψ0, hψzero, ?_⟩
  have hcont : Continuous (fderiv ℝ (N.reducedFieldJoint x₀)) :=
    (N.reducedFieldJoint_contDiff x₀).continuous_fderiv one_ne_zero
  have hψc : ContinuousAt ψ ρ := hψcd.continuousAt
  have hpath : ContinuousAt (fun ρ' => (ρ', ψ ρ')) ρ := continuousAt_id.prodMk hψc
  have hF : ContinuousAt (fun ρ' => fderiv ℝ (N.reducedFieldJoint x₀) (ρ', ψ ρ')) ρ :=
    hcont.continuousAt.comp hpath
  have hg : ContinuousAt (fun ρ' => (fderiv ℝ (N.reducedFieldJoint x₀) (ρ', ψ ρ'))
      ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)) ρ := by
    rw [continuousAt_clm_apply]
    intro y
    have hz := (continuousAt_clm_apply.mp hF)
      (ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ) y)
    simpa [ContinuousLinearMap.comp_apply] using hz
  have hdetcont : ContinuousAt (fun ρ' => LinearMap.det
      ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ', ψ ρ'))
        ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap) ρ := by
    exact ContinuousLinearMap.continuous_det.continuousAt.comp hg
  have hdet0 : LinearMap.det (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap ≠ 0 := by
    by_contra hcon
    have h1 : LinearMap.ker (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap ≠ ⊥ := by
      rw [← LinearMap.det_eq_zero_iff_ker_ne_bot]
      exact hcon
    have h2 : LinearMap.ker (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr hns.injective
    exact h1 h2
  have hdetAt : LinearMap.det ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ, ψ ρ))
        ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap
      = LinearMap.det (N.reducedJacobianCLMAtRate ρ x₀ y).toLinearMap := by
    have h := N.fderiv_reducedFieldJoint_inr x₀ ρ (ψ ρ)
    rw [h, hψ0]
  have hdet0' : LinearMap.det ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ, ψ ρ))
        ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap ≠ 0 := by
    rw [hdetAt]
    exact hdet0
  have hsign : ∀ᶠ ρ' in 𝓝 ρ,
      ((SignType.sign (LinearMap.det
          ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ', ψ ρ'))
            ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap)
            : SignType) : ℤ)
        = ((SignType.sign (LinearMap.det
          ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ, ψ ρ))
            ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap)
            : SignType) : ℤ) := by
    rcases lt_trichotomy
        (LinearMap.det ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ, ψ ρ))
          ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap) 0 with
        h | h | h
    · filter_upwards [hdetcont.eventually_lt continuousAt_const (g := fun _ => (0 : ℝ)) h] with ρ' hρ'
      rw [sign_neg hρ', sign_neg h]
    · exact absurd h hdet0'
    · filter_upwards [continuousAt_const.eventually_lt hdetcont (f := fun _ => (0 : ℝ)) h] with ρ' hρ'
      rw [sign_pos hρ', sign_pos h]
  filter_upwards [hsign] with ρ' hρ'
  have hconv : LinearMap.det (N.reducedJacobianCLMAtRate ρ' x₀ (ψ ρ')).toLinearMap
      = LinearMap.det ((fderiv ℝ (N.reducedFieldJoint x₀) (ρ', ψ ρ'))
        ∘L ContinuousLinearMap.inr ℝ (N.R → ℝ) (Fin N.stoichRank → ℝ)).toLinearMap := by
    have h := N.fderiv_reducedFieldJoint_inr x₀ ρ' (ψ ρ')
    rw [h]
  unfold reducedFieldOrientationSign
  rw [hconv, ← hdetAt]
  exact hρ'

/-! ## The field is affine in the rate constants -/

/-- **The mass-action field is affine in the rate constants.**  At a fixed concentration the
field depends *linearly* on the rate vector. -/
theorem massActionVectorFieldAtRate_add (N : Network S) (ρ₁ ρ₂ : N.R → ℝ)
    (x : Concentration S) :
    N.massActionVectorFieldAtRate (ρ₁ + ρ₂) x
      = N.massActionVectorFieldAtRate ρ₁ x + N.massActionVectorFieldAtRate ρ₂ x := by
  funext s
  simp only [massActionVectorFieldAtRate, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The mass-action field vanishes at the zero rate vector. -/
theorem massActionVectorFieldAtRate_zero (N : Network S) (x : Concentration S) :
    N.massActionVectorFieldAtRate (0 : N.R → ℝ) x = 0 := by
  funext s
  simp [massActionVectorFieldAtRate]

/-- **The reduced field is affine in the rate constants.** -/
theorem reducedFieldAtRate_add (N : Network S) (ρ₁ ρ₂ : N.R → ℝ) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) :
    N.reducedFieldAtRate (ρ₁ + ρ₂) x₀ y
      = N.reducedFieldAtRate ρ₁ x₀ y + N.reducedFieldAtRate ρ₂ x₀ y := by
  simp only [reducedFieldAtRate, massActionVectorFieldAtRate_add, map_add]

/-! ## The reduced Jacobian when the ambient Jacobian is a scalar on the stoichiometric subspace -/

/-- **The reduced Jacobian is the ambient Jacobian restricted to the stoichiometric subspace.**
If the ambient Jacobian `J` acts on the stoichiometric subspace as the scalar `lam`, then the
compression `stoichProj ∘ J ∘ stoichChart` — the reduced Jacobian — is `lam` times the identity on
the class coordinates.  This is the nondegeneracy criterion for a CRN equilibrium read in the
class: the equilibrium is nondegenerate exactly when the ambient Jacobian does not annihilate the
class direction. -/
theorem reducedJacobianCLM_eq_smul_id_of (N : Network S)
    (J : Concentration S →L[ℝ] Concentration S) (lam : ℝ)
    (hJ : ∀ w ∈ N.stoichSubspace, J w = lam • w) :
    N.stoichProj.comp (J.comp N.stoichChart) = lam • (ContinuousLinearMap.id ℝ (Fin N.stoichRank → ℝ)) := by
  have hmem : ∀ y', N.stoichChart y' ∈ N.stoichSubspace := fun y' => N.stoichChart_mem y'
  have h1 : J ∘L N.stoichChart = lam • N.stoichChart := by
    ext y'
    simp only [smul_apply, ContinuousLinearMap.comp_apply]
    rw [hJ (N.stoichChart y') (hmem y')]
  rw [h1]
  ext y'
  simp only [ContinuousLinearMap.comp_apply, smul_apply]
  rw [map_smul, N.stoichProj_stoichChart]
  rfl

/-- **The reduced Jacobian is the ambient Jacobian restricted to the stoichiometric subspace.**
If the ambient Jacobian `J` acts on the stoichiometric subspace as the scalar `lam`, then the
reduced Jacobian — the compression `stoichProj ∘ J ∘ stoichChart` — is `lam` times the identity on
the class coordinates. -/
theorem reducedJacobianCLM_eq_smul_id (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) (lam : ℝ)
    (hJ : ∀ w ∈ N.stoichSubspace,
      N.massActionJacobianCLM κ (N.affineChart x₀ y) w = lam • w) :
    N.reducedJacobianCLM κ x₀ y = lam • (ContinuousLinearMap.id ℝ (Fin N.stoichRank → ℝ)) := by
  rw [reducedJacobianCLM]
  exact reducedJacobianCLM_eq_smul_id_of N (N.massActionJacobianCLM κ (N.affineChart x₀ y)) lam hJ

/-- The rate-vector version of `reducedJacobianCLM_eq_smul_id`. -/
theorem reducedJacobianCLMAtRate_eq_smul_id (N : Network S) (ρ : N.R → ℝ) (x₀ : Concentration S)
    (y : Fin N.stoichRank → ℝ) (lam : ℝ)
    (hJ : ∀ w ∈ N.stoichSubspace,
      N.massActionJacobianCLMAtRate ρ (N.affineChart x₀ y) w = lam • w) :
    N.reducedJacobianCLMAtRate ρ x₀ y = lam • (ContinuousLinearMap.id ℝ (Fin N.stoichRank → ℝ)) := by
  rw [reducedJacobianCLMAtRate]
  exact reducedJacobianCLM_eq_smul_id_of N (N.massActionJacobianCLMAtRate ρ (N.affineChart x₀ y))
    lam hJ

/-! ## A worked instance: the reversible pair `A ⇌ B` -/

namespace RevPair

open Finset

/-- The complex `A`. -/
def a : Complex (Fin 2) := ![1, 0]

/-- The complex `B`. -/
def b : Complex (Fin 2) := ![0, 1]

/-- **The reversible pair `A ⇌ B`.**  Reaction `0` is `A → B`, reaction `1` is `B → A`. -/
def N : Network (Fin 2) where
  R := Fin 2
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun i => if i = 0 then ⟨a, b⟩ else ⟨b, a⟩

/-- The stoichiometric reaction vector of `A → B`. -/
theorem reactionVector_zero : N.reactionVector (0 : Fin 2) = ![-1, 1] := by
  funext s
  fin_cases s <;> simp [N, a, b, Network.reactionVector_apply]

/-- The stoichiometric reaction vector of `B → A`. -/
theorem reactionVector_one : N.reactionVector (1 : Fin 2) = ![1, -1] := by
  funext s
  fin_cases s <;> simp [N, a, b, Network.reactionVector_apply]
/-- The rate vector of the reversible pair: forward rate `kf`, backward rate `kr`. -/
def rates (kf kr : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then kf else kr

/-- The `A`-component of the mass-action field of the reversible pair. -/
theorem massActionVectorFieldAtRate_zero (kf kr : ℝ) (x : Concentration (Fin 2)) :
    N.massActionVectorFieldAtRate (rates kf kr) x 0 = kr * x 1 - kf * x 0 := by
  have h : N.massActionVectorFieldAtRate (rates kf kr) x 0
      = ∑ r : Fin 2, (rates kf kr r * (N.reaction r).source.massActionMonomial x)
          * N.reactionVector r 0 := by
    simp only [massActionVectorFieldAtRate]
    rfl
  rw [h, Fin.sum_univ_two]
  simp [N, rates, a, b, Network.reactionVector_apply, Complex.massActionMonomial,
    Fin.prod_univ_succ]
  ring

/-- The `B`-component of the mass-action field of the reversible pair. -/
theorem massActionVectorFieldAtRate_one (kf kr : ℝ) (x : Concentration (Fin 2)) :
    N.massActionVectorFieldAtRate (rates kf kr) x 1 = kf * x 0 - kr * x 1 := by
  have h : N.massActionVectorFieldAtRate (rates kf kr) x 1
      = ∑ r : Fin 2, (rates kf kr r * (N.reaction r).source.massActionMonomial x)
          * N.reactionVector r 1 := by
    simp only [massActionVectorFieldAtRate]
    rfl
  rw [h, Fin.sum_univ_two]
  simp [N, rates, a, b, Network.reactionVector_apply, Complex.massActionMonomial,
    Fin.prod_univ_succ]
  ring

/-- **The mass-action field of the reversible pair.**  The two species exchange at rates
`kf` and `kr`; the field is `x ↦ (kr x_B - kf x_A, kf x_A - kr x_B)`. -/
theorem massActionVectorFieldAtRate_eq (kf kr : ℝ) (x : Concentration (Fin 2)) :
    N.massActionVectorFieldAtRate (rates kf kr) x
      = ![kr * x 1 - kf * x 0, kf * x 0 - kr * x 1] := by
  funext s
  fin_cases s
  · exact massActionVectorFieldAtRate_zero kf kr x
  · exact massActionVectorFieldAtRate_one kf kr x

/-- **The equilibrium of the reversible pair in the class of total concentration `c`.**  The
equilibrium is a *rational* function of the rates: `x_A = c k_r/(k_f + k_r)` and
`x_B = c k_f/(k_f + k_r)`. -/
noncomputable def equilibrium (kf kr c : ℝ) : Concentration (Fin 2) :=
  ![c * kr / (kf + kr), c * kf / (kf + kr)]

/-- **The explicit equilibrium is a steady state of the reversible pair.** -/
theorem massActionVectorFieldAtRate_equilibrium (kf kr c : ℝ) (h : kf + kr ≠ 0) :
    N.massActionVectorFieldAtRate (rates kf kr) (equilibrium kf kr c) = 0 := by
  rw [massActionVectorFieldAtRate_eq]
  ext s
  fin_cases s <;> simp [equilibrium] <;> field_simp <;> ring

/-- **The equilibrium is the unique steady state in its class.** -/
theorem eq_equilibrium_of_steadyState (kf kr c : ℝ) (h : kf + kr ≠ 0) (x : Concentration (Fin 2))
    (hx : N.massActionVectorFieldAtRate (rates kf kr) x = 0) (hclass : x 0 + x 1 = c) :
    x = equilibrium kf kr c := by
  rw [massActionVectorFieldAtRate_eq] at hx
  have h0 : kr * x 1 - kf * x 0 = 0 := by simpa using congrFun hx 0
  have h1 : kf * x 0 - kr * x 1 = 0 := by simpa using congrFun hx 1
  have hrel : kr * x 1 = kf * x 0 := by linarith
  have hx1 : x 1 = c * kf / (kf + kr) := by
    have hthis : (kf + kr) * x 1 = kf * c := by
      calc (kf + kr) * x 1 = kf * x 1 + kr * x 1 := by ring
        _ = kf * x 1 + kf * x 0 := by rw [hrel]
        _ = kf * (x 0 + x 1) := by ring
        _ = kf * c := by rw [hclass]
    have h1' : x 1 * (kf + kr) = c * kf := by linear_combination hthis
    exact (eq_div_iff h).2 h1'
  have hx0 : x 0 = c * kr / (kf + kr) := by
    have hthis : x 0 = c - x 1 := by linarith
    have h0' : x 0 * (kf + kr) = c * kr := by
      rw [hthis, hx1]
      field_simp
      ring
    exact (eq_div_iff h).2 h0'
  ext s
  fin_cases s <;> simp [equilibrium, hx0, hx1]

/-- **The equilibrium of the reversible pair depends smoothly on the rates.**  It is a rational
function of the rates, hence real-analytic wherever `k_f + k_r ≠ 0`. -/
theorem equilibrium_contDiffAt (kf kr c : ℝ) (h : kf + kr ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => equilibrium p.1 p.2 c) (kf, kr) := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · show ContDiffAt ℝ 1 (fun p : ℝ × ℝ => c * p.2 / (p.1 + p.2)) (kf, kr)
    exact (contDiffAt_const.mul contDiffAt_snd).div
      (contDiffAt_fst.add contDiffAt_snd) (by simpa using h)
  · show ContDiffAt ℝ 1 (fun p : ℝ × ℝ => c * p.1 / (p.1 + p.2)) (kf, kr)
    exact (contDiffAt_const.mul contDiffAt_fst).div
      (contDiffAt_fst.add contDiffAt_snd) (by simpa using h)

/-- **The equilibrium of the reversible pair is a real-analytic function of the rates.**
It is a rational function of the rates, hence analytic wherever `k_f + k_r ≠ 0`. -/
theorem equilibrium_component_analyticAt (kf kr c : ℝ) (h : kf + kr ≠ 0) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => c * p.2 / (p.1 + p.2)) (kf, kr) := by
  have hne : (fun p : ℝ × ℝ => p.1 + p.2) (kf, kr) ≠ 0 := by simpa using h
  have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (kf, kr) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt _
  have hsnd : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) (kf, kr) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt _
  fun_prop

/-- The equilibrium of the reversible pair is `C¹` on the region of non-cancelling rates. -/
theorem equilibrium_contDiffOn (c : ℝ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => equilibrium p.1 p.2 c) {p | p.1 + p.2 ≠ 0} := by
  intro p hp
  exact (equilibrium_contDiffAt p.1 p.2 c hp).contDiffWithinAt

/-- **The Jacobian of the reversible pair is constant.**  It is the operator
`u ↦ (k_f u_A) · (-1,1) + (k_r u_B) · (1,-1)`. -/
theorem massActionJacobianCLMAtRate_apply (kf kr : ℝ) (x u : Concentration (Fin 2)) :
    N.massActionJacobianCLMAtRate (rates kf kr) x u
      = (kf * u 0) • ![-1, 1] + (kr * u 1) • ![1, -1] := by
  have hF : HasFDerivAt (fun y : Concentration (Fin 2) =>
      ![kr * y 1 - kf * y 0, kf * y 0 - kr * y 1])
      (ContinuousLinearMap.pi (fun i : Fin 2 =>
        if i = 0 then
          kr • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) -
            kf • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)
        else
          kf • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) -
            kr • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1))) x := by
    refine hasFDerivAt_pi.2 (fun i => ?_)
    fin_cases i
    · exact HasFDerivAt.sub ((hasFDerivAt_apply 1 x).const_mul kr) ((hasFDerivAt_apply 0 x).const_mul kf)
    · exact HasFDerivAt.sub ((hasFDerivAt_apply 0 x).const_mul kf) ((hasFDerivAt_apply 1 x).const_mul kr)
  have hJ : N.massActionJacobianCLMAtRate (rates kf kr) x
      = ContinuousLinearMap.pi (fun i : Fin 2 =>
        if i = 0 then
          kr • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) -
            kf • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)
        else
          kf • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) -
            kr • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) := by
    have h := N.massActionVectorFieldAtRate_hasFDerivAt (rates kf kr) x
    rw [show (fun y => N.massActionVectorFieldAtRate (rates kf kr) y)
        = fun y => ![kr * y 1 - kf * y 0, kf * y 0 - kr * y 1] by
      funext y; exact massActionVectorFieldAtRate_eq kf kr y] at h
    exact h.unique hF
  rw [hJ]
  ext s
  fin_cases s
  · simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, smul_apply,
      Pi.add_apply, smul_eq_mul]
    ring
  · simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, smul_apply,
      Pi.add_apply, smul_eq_mul]
    ring

/-- **The Jacobian of the reversible pair acts on the stoichiometric subspace as the scalar
`-(k_f + k_r)`.**  This is the nondegeneracy of the reversible pair: the equilibrium does not
annihilate the class direction. -/
theorem massActionJacobianCLMAtRate_stoichSubspace (kf kr : ℝ) (x : Concentration (Fin 2)) :
    ∀ w ∈ N.stoichSubspace,
      N.massActionJacobianCLMAtRate (rates kf kr) x w = -(kf + kr) • w := by
  intro w hw
  refine Submodule.span_induction
    (p := fun w _ => N.massActionJacobianCLMAtRate (rates kf kr) x w = -(kf + kr) • w) ?_ ?_ ?_ ?_ hw
  · intro u hu
    obtain ⟨r, rfl⟩ := hu
    have hr : r = (0 : Fin 2) ∨ r = (1 : Fin 2) := by
      refine Fin.cases (motive := fun r : Fin 2 => r = (0 : Fin 2) ∨ r = (1 : Fin 2))
        (Or.inl rfl) (fun i => Or.inr (Fin.ext_iff.mpr (by
          rw [Fin.val_succ, Fin.val_one]; have hi := i.isLt; omega))) r
    rcases hr with hr | hr
    · rw [hr, massActionJacobianCLMAtRate_apply, reactionVector_zero]
      ext s
      fin_cases s
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    · rw [hr, massActionJacobianCLMAtRate_apply, reactionVector_one]
      ext s
      fin_cases s
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp
  · intro u v hu hv hpu hpv
    rw [map_add, hpu, hpv]
    ext s
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro c u hu hpu
    rw [map_smul, hpu]
    ext s
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- **The reduced Jacobian of the reversible pair is `-(k_f + k_r)` times the identity.**  Hence
the equilibrium of the reversible pair is nondegenerate exactly when `k_f + k_r ≠ 0`, and
`equilibrium_smooth_of_nonSingular` then applies. -/
theorem reducedJacobianCLMAtRate_eq (kf kr : ℝ) (x₀ : Concentration (Fin 2))
    (y : Fin N.stoichRank → ℝ) :
    N.reducedJacobianCLMAtRate (rates kf kr) x₀ y
      = -(kf + kr) • (ContinuousLinearMap.id ℝ (Fin N.stoichRank → ℝ)) := by
  refine N.reducedJacobianCLMAtRate_eq_smul_id (rates kf kr) x₀ y (-(kf + kr)) ?_
  intro w hw
  exact massActionJacobianCLMAtRate_stoichSubspace kf kr (N.affineChart x₀ y) w hw

end RevPair

end Network

end CRNT

#print axioms CRNT.Network.equilibrium_smooth_of_nonSingular
#print axioms CRNT.Network.reducedFieldOrientationSign_eventually_eq_of_nonSingular
#print axioms CRNT.Network.reducedFieldAtRate_joint_contDiff
#print axioms CRNT.Network.reducedJacobianCLM_eq_smul_id
#print axioms CRNT.Network.reducedJacobianCLMAtRate_eq_smul_id
#print axioms CRNT.Network.RevPair.reducedJacobianCLMAtRate_eq
#print axioms CRNT.Network.RevPair.equilibrium_contDiffAt
#print axioms CRNT.Network.RevPair.equilibrium_component_analyticAt
