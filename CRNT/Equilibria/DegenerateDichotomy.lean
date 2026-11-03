import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Examples.ReversiblePair

/-!
# The isolation criterion for a complex-balanced equilibrium

## The classical picture

Horn and Jackson (*The theory of open chemical reaction networks*, 1972, Theorem 6.4) describe
the complex-balanced equilibria of a network as a **union of toric sets**: relative to a
complex-balanced reference `x*`, the *toric set* is

```text
T(x*) = { x > 0 | log(x / x*) ⟂ S(N) },
```

the set of positive points whose log-ratio to `x*` is orthogonal to the stoichiometric subspace
`S(N)`.  Complex balance propagates along the torus action `x ↦ x · exp u` (`u ⟂ S(N)`), and
Craciun (*Toric differential inclusions*, 2006) uses this to read the complex-balanced set as
a union of orbits of the monomial rescaling group.

The **degenerate / non-degenerate dichotomy** is the statement that a class carries either a
single complex-balanced equilibrium (the *non-degenerate* case, in which the equilibrium is
isolated) or a positive-dimensional toric set (the *degenerate* case).  This module records the
*reachable* form of that dichotomy, in the vocabulary of the repository:

* the **isolation criterion** (`unique_complexBalanced_of_nondegenerate`): a complex-balanced
  equilibrium whose reduced Jacobian is invertible on the stoichiometric subspace is the unique
  complex-balanced equilibrium of its compatibility class;
* the **toric-orbit statement** (`two_complexBalanced_differ_by_monomial_rescaling`): two
  positive complex-balanced concentrations differ by a monomial rescaling whose direction lies
  in the kernel of the reaction matrix;
* the **transversality** of that action (`eq_of_same_class_of_monomial_rescaling`): a toric
  orbit meets any compatibility class in at most one point.

## What the repository already provides

* leaf **S17** (`CRNT.Equilibria.ToricSteadyStates`, `CRNT.Equilibria.ToricCriterion`,
  `CRNT.Equilibria.ToricParametrization`): the toric (log-affine) parametrisation of the
  steady-state variety, `CRNT.Network.toricSteadyState_iff_log_orthogonal` and
  `CRNT.Network.toricSteadyState_iff_exp_parametrization`;
* the toric machinery of `CRNT.Theorems.DeficiencyZero.Toric`: the toric inclusion
  `CRNT.Network.complexBalanced_of_logRatio_orthogonal`, the **converse** toric inclusion
  `CRNT.Network.logRatio_orthogonal_of_complexBalanced`, the Horn–Jackson uniqueness
  `CRNT.Network.isComplexBalanced_unique_in_positiveClass`, and the existence statement
  `CRNT.Network.exists_isComplexBalanced_in_positiveClass`;
* leaf **D21** (`CRNT.Equilibria.ComplexBalanceLinearStability`): the linearisation theorem —
  the entropy-Hessian pairing of the mass-action Jacobian is strictly negative on nonzero
  stoichiometric perturbations (`CRNT.Network.complexBalanceJacobianQuadratic_strict_on_stoich`),
  hence the Jacobian has no kernel vector tangent to a class
  (`CRNT.Network.complexBalanceJacobian_injective_on_stoich`).

## What this module adds

* the **nondegeneracy criterion** in the repository's terms (`IsNondegenerateAt`: the
  mass-action Jacobian is injective on the stoichiometric subspace), together with its
  characterisation as the injectivity of the reduced Jacobian
  (`isNondegenerate_iff_injective_reducedJacobian`) and, at a complex-balanced equilibrium, as
  the strict entropy dissipation of the Horn–Jackson quadratic form
  (`isNondegenerate_iff_strict_dissipation`);
* the **Horn–Jackson uniqueness without the weak-reversibility hypothesis**
  (`unique_complexBalanced_in_positiveClass`): a positive complex-balanced equilibrium forces
  weak reversibility (`CRNT.Network.weaklyReversible_of_positive_complexBalanced`), so the
  complex-balanced equilibrium of a positive compatibility class is unique for *every* network
  with a positive complex-balanced equilibrium;
* the **isolation criterion** `unique_complexBalanced_of_nondegenerate` in the form asked for;
* the **one complex-balanced equilibrium per positive class**
  (`exists_unique_isComplexBalanced_in_positiveClass`);
* the **toric-orbit statement** `two_complexBalanced_differ_by_monomial_rescaling` and the
  identification of `orthSum S(N)` with the kernel of the reaction matrix
  (`mem_orthSum_stoichSubspace_iff`);
* the **transversality** of the torus action on the compatibility classes
  (`eq_of_same_class_of_monomial_rescaling`);
* a **worked instance**: the reversible pair `A ⇌ B`
  (`CRNT.Examples.ReversiblePair.isComplexBalanced_iff`: the complex-balanced set is the ray
  through the equilibrium; `CRNT.Examples.ReversiblePair.equilibrium_isNondegenerate` and
  `CRNT.Examples.ReversiblePair.equilibrium_unique_complexBalanced_in_class`).

## What remains open

* The **full polytope form** of the dichotomy — the complex-balanced set of a class being a
  finite union of toric sets indexed by the *faces of a Newton polytope* — is **not** proved
  here: it needs the combinatorics of faces of a polytope (the face lattice, the adjacency
  structure of the Newton polytope of the network), which Mathlib does not provide.  What is
  proved here is the *reachability* half: the complex-balanced set is a union of monomial
  rescaling orbits, and each orbit meets a compatibility class in at most one point.
* The **degeneracy criterion** in the classical sense of Craciun — the equivalence between the
  singularity of the reduced Jacobian and the tangency of a toric orbit to the class, and the
  consequent local-degree argument (`CRNT.Multistationarity.DegreeStructural`) that isolates a
  non-degenerate equilibrium among *all* the steady states of its class — is not proved here.
  Note that in the mass-action formulation used by this repository, the linearisation of the
  vector field restricted to the stoichiometric subspace is *always* invertible at a positive
  complex-balanced equilibrium (leaf D21), so the isolation content of nondegeneracy concerns
  the steady-state equations, not the dynamics.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The nondegeneracy criterion -/

/-- **Nondegeneracy of a steady state.**  The steady state `x` is *nondegenerate* when the
mass-action Jacobian at `x` is injective on the stoichiometric subspace `S(N)`; equivalently,
the *reduced Jacobian* — the compression of the mass-action Jacobian to `S(N)` — is invertible
on `S(N)`.  This is the Craciun–Feinberg nondegeneracy condition in the coordinate-free form
used by this repository (leaf D21). -/
def IsNondegenerateAt (N : Network S) (κ : N.RateConstants) (x : Concentration S) : Prop :=
  ∀ h ∈ N.stoichSubspace, (N.massActionJacobian κ x).mulVec h = 0 → h = 0

/-- **The mass-action Jacobian maps into the stoichiometric subspace.**  The linearisation of
the mass-action field is a reaction vector field, so it takes values in `S(N)`. -/
theorem massActionJacobian_mulVec_mem_stoichSubspace (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (h : Concentration S) :
    (N.massActionJacobian κ x).mulVec h ∈ N.stoichSubspace := by
  rw [N.massActionJacobian_mulVec_logform κ hx h]
  have hshape : (fun s => ∑ r : N.R, N.massActionRate κ r x *
        (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / x j)) * N.reactionVector r s)
      = ∑ r : N.R, fun s => N.massActionRate κ r x *
        (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / x j)) * N.reactionVector r s := by
    funext s
    rw [Finset.sum_apply]
  rw [hshape]
  refine N.stoichSubspace.sum_mem fun r _ => ?_
  refine N.stoichSubspace.smul_mem _ ?_
  exact N.reactionVector_mem_stoichSubspace r

/-- The chart coordinate of a point relative to itself is zero. -/
theorem chartCoord_self (N : Network S) (x : Concentration S) : N.chartCoord x x = 0 := by
  simp only [chartCoord, sub_self]
  exact ContinuousLinearMap.map_zero N.stoichProj

/-- The affine chart at the origin is the point itself. -/
theorem affineChart_zero (N : Network S) (x : Concentration S) : N.affineChart x 0 = x := by
  simp only [affineChart, ContinuousLinearMap.map_zero, add_zero]

/-- **The reduced Jacobian at a class point acts by the projection of the mass-action
Jacobian along the chart.**  This is the coordinate form of the reduced Jacobian of
`CRNT.Multistationarity.ReducedJacobian`: at the chart coordinate of `x` it reads the
compression `stoichProj ∘ J(x) ∘ stoichChart`. -/
theorem reducedJacobianCLM_apply (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (y : Fin N.stoichRank → ℝ) :
    N.reducedJacobianCLM κ x (N.chartCoord x x) y
      = N.stoichProj ((N.massActionJacobian κ x).mulVec (N.stoichChart y)) := by
  rw [reducedJacobianCLM, N.chartCoord_self, N.affineChart_zero]
  simp only [ContinuousLinearMap.comp_apply]
  rw [N.massActionJacobianCLM_apply]

/-- **The nondegeneracy of a complex-balanced equilibrium is the injectivity of the reduced
Jacobian on the stoichiometric subspace.**  The reduced Jacobian of the class — the
`s × s` compression of the mass-action Jacobian built by `CRNT.Multistationarity.StoichChart` —
is invertible exactly when the mass-action Jacobian is injective on the stoichiometric
subspace. -/
theorem isNondegenerate_iff_injective_reducedJacobian (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    N.IsNondegenerateAt κ x ↔
      Function.Injective (N.reducedJacobianCLM κ x (N.chartCoord x x)) := by
  constructor
  · intro hnd y hy hR_eq
    have hmemY : N.stoichChart y ∈ N.stoichSubspace := N.stoichChart_mem y
    have hmemH : N.stoichChart hy ∈ N.stoichSubspace := N.stoichChart_mem hy
    have hJY : (N.massActionJacobian κ x).mulVec (N.stoichChart y) ∈ N.stoichSubspace :=
      N.massActionJacobian_mulVec_mem_stoichSubspace κ hx (N.stoichChart y)
    have hJH : (N.massActionJacobian κ x).mulVec (N.stoichChart hy) ∈ N.stoichSubspace :=
      N.massActionJacobian_mulVec_mem_stoichSubspace κ hx (N.stoichChart hy)
    have hproj : N.stoichProj ((N.massActionJacobian κ x).mulVec (N.stoichChart y))
        = N.stoichProj ((N.massActionJacobian κ x).mulVec (N.stoichChart hy)) := by
      have h' := hR_eq
      rwa [reducedJacobianCLM_apply N κ, reducedJacobianCLM_apply N κ] at h'
    have hJYeq : (N.massActionJacobian κ x).mulVec (N.stoichChart y)
        = (N.massActionJacobian κ x).mulVec (N.stoichChart hy) := by
      calc (N.massActionJacobian κ x).mulVec (N.stoichChart y)
          = N.stoichChart (N.stoichProj ((N.massActionJacobian κ x).mulVec (N.stoichChart y))) :=
            (N.stoichChart_stoichProj hJY).symm
        _ = N.stoichChart (N.stoichProj ((N.massActionJacobian κ x).mulVec (N.stoichChart hy))) := by
            rw [hproj]
        _ = (N.massActionJacobian κ x).mulVec (N.stoichChart hy) :=
            (N.stoichChart_stoichProj hJH)
    have hdiff : N.stoichChart y - N.stoichChart hy ∈ N.stoichSubspace :=
      N.stoichSubspace.sub_mem hmemY hmemH
    have hJdiff : (N.massActionJacobian κ x).mulVec (N.stoichChart y - N.stoichChart hy) = 0 := by
      rw [Matrix.mulVec_sub, hJYeq]
      simp
    have hzero : N.stoichChart y - N.stoichChart hy = 0 := hnd _ hdiff hJdiff
    have hchart : N.stoichChart y = N.stoichChart hy := by
      have h' := sub_eq_zero.mp hzero
      simpa using h'
    exact N.stoichChart_injective hchart
  · intro hR h hS hJ
    have hchart : N.stoichChart (N.stoichProj h) = h := N.stoichChart_stoichProj hS
    have hR0 : N.reducedJacobianCLM κ x (N.chartCoord x x) (N.stoichProj h)
        = N.reducedJacobianCLM κ x (N.chartCoord x x) 0 := by
      rw [reducedJacobianCLM_apply N κ, reducedJacobianCLM_apply N κ, hchart, hJ]
      simp
    have hproj : N.stoichProj h = 0 := hR hR0
    have : h = 0 := by
      calc h = N.stoichChart (N.stoichProj h) := hchart.symm
        _ = N.stoichChart 0 := by rw [hproj]
        _ = 0 := by simp
    exact this

/-- **A complex-balanced equilibrium of a weakly reversible network is nondegenerate.**  The
linearisation theorem (leaf D21) gives strict entropy dissipation along every nonzero
stoichiometric perturbation, hence no nonzero kernel vector tangent to a class. -/
theorem complexBalanced_isNondegenerate (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) : N.IsNondegenerateAt κ xstar :=
  fun h hS hJ => N.complexBalanceJacobian_injective_on_stoich κ hwr hxs hcb h hS hJ

/-- **The nondegeneracy of a complex-balanced equilibrium is the strict dissipation of the
Horn–Jackson entropy along the stoichiometric perturbations.**  At a positive complex-balanced
equilibrium the two are equivalent: the reduced Jacobian is invertible on `S(N)` exactly when
the entropy-Hessian pairing of the mass-action Jacobian is strictly negative on every nonzero
stoichiometric perturbation.  (The right-hand side always holds at such an equilibrium, by the
linearisation theorem of leaf D21.) -/
theorem isNondegenerate_iff_strict_dissipation (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.IsNondegenerateAt κ xstar ↔
      ∀ h ∈ N.stoichSubspace, h ≠ 0 → N.complexBalanceJacobianQuadratic κ xstar h < 0 := by
  constructor
  · intro _
    exact fun h hS h0 => N.complexBalanceJacobianQuadratic_strict_on_stoich κ hwr hxs hcb hS h0
  · intro hnd h hS hJ
    by_contra hne
    have hneg := hnd h hS hne
    have hzero : N.complexBalanceJacobianQuadratic κ xstar h = 0 := by
      rw [complexBalanceJacobianQuadratic, entropyHessianPairing, hJ]
      simp
    linarith [hneg, hzero]

/-! ## The isolation criterion -/

/-- **Uniqueness of the complex-balanced equilibrium in a positive compatibility class.**
A positive complex-balanced equilibrium forces weak reversibility, so the Horn–Jackson
uniqueness theorem applies: the complex-balanced equilibrium of a positive compatibility class
is unique, for *every* network with a positive complex-balanced equilibrium. -/
theorem unique_complexBalanced_in_positiveClass (N : Network S) (κ : N.RateConstants)
    {xstar y : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hy : y ∈ N.positiveCompatibilityClass xstar) (hcby : N.IsComplexBalanced κ y) :
    y = xstar := by
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  have hstar : xstar ∈ N.positiveCompatibilityClass xstar := by
    refine ⟨?_, hxs⟩
    simp [StoichCompatible]
  exact N.isComplexBalanced_unique_in_positiveClass hwr κ hy hstar hcby hcb

/-- **The isolation criterion.**  A *nondegenerate* complex-balanced equilibrium `x*` — one
whose reduced Jacobian is invertible on the stoichiometric subspace — is a nondegenerate steady
state and the **unique** complex-balanced equilibrium in its compatibility class.

This is the reachable form of the Horn–Jackson dichotomy: the complex-balanced set of a class
is a union of toric orbits, and a point at which the reduced Jacobian is invertible is an orbit
of dimension zero.  (In the mass-action formulation of this repository the uniqueness of the
complex-balanced equilibrium in the class holds unconditionally — the nondegeneracy hypothesis
is what makes the equilibrium *isolated among all the steady states* of the class, a statement
that is not proved here.) -/
theorem unique_complexBalanced_of_nondegenerate (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnd : N.IsNondegenerateAt κ xstar) :
    N.IsNondegenerateAt κ xstar ∧
      ∀ y : Concentration S, y ∈ N.positiveCompatibilityClass xstar →
        N.IsComplexBalanced κ y → y = xstar := by
  refine ⟨hnd, ?_⟩
  intro y hy hcb_y
  exact N.unique_complexBalanced_in_positiveClass κ hxs hcb hy hcb_y

/-- **One complex-balanced equilibrium per positive compatibility class.**  Every positive
compatibility class contains a complex-balanced equilibrium (the toric inclusion, by Birch
existence), and it is unique (Horn–Jackson).  This is the dichotomy in its "reachable" form:
the class carries exactly one complex-balanced equilibrium, which is the point of its toric
orbit. -/
theorem exists_unique_isComplexBalanced_in_positiveClass (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar) :
    ∀ x₀ : Concentration S, x₀.Positive →
      ∃! y : Concentration S, y ∈ N.positiveCompatibilityClass x₀ ∧ N.IsComplexBalanced κ y := by
  intro x₀ hx₀
  obtain ⟨y, hy, hcb_y⟩ := N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  refine ⟨y, ⟨hy, hcb_y⟩, ?_⟩
  intro z hz
  obtain ⟨hzmem, hcb_z⟩ := hz
  have hwr : N.WeaklyReversible := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  exact N.isComplexBalanced_unique_in_positiveClass hwr κ hzmem hy hcb_z hcb_y

/-! ## The toric orbits -/

/-- **The kernel of the reaction matrix.**  A vector `u` lies in the kernel of the reaction
(stoichiometric) matrix exactly when it is orthogonal to the stoichiometric subspace, that is,
when it pairs to zero with every reaction vector. -/
theorem mem_orthSum_stoichSubspace_iff (N : Network S) (u : S → ℝ) :
    u ∈ orthSum N.stoichSubspace ↔ ∀ r : N.R, ∑ s : S, u s * N.reactionVector r s = 0 := by
  constructor
  · intro h r
    exact (mem_orthSum.mp h) (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
  · intro h
    refine mem_orthSum_span ?_
    intro g hg
    obtain ⟨r, rfl⟩ := hg
    exact h r

/-- **A monomial rescaling of a complex-balanced equilibrium is complex-balanced.**  This is
the toric inclusion in monomial form: the torus action `x ↦ x · exp u` with `u ⟂ S(N)`
preserves complex balance. -/
theorem isComplexBalanced_of_monomial_rescaling (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (u : S → ℝ) (hu : u ∈ orthSum N.stoichSubspace) :
    N.IsComplexBalanced κ (fun s => xstar s * Real.exp (u s)) := by
  have hlog : ∀ s, Real.log (xstar s * Real.exp (u s)) - Real.log (xstar s) = u s := by
    intro s
    rw [Real.log_mul (hxs s).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine N.complexBalanced_of_logRatio_orthogonal κ
    (fun s => mul_pos (hxs s) (Real.exp_pos _)) hxs hcb ?_
  rw [mem_orthSum]
  intro v hv
  calc ∑ s, (Real.log (xstar s * Real.exp (u s)) - Real.log (xstar s)) * v s
      = ∑ s, u s * v s := Finset.sum_congr rfl fun s _ => by rw [hlog s]
    _ = 0 := (mem_orthSum.mp hu) v hv

/-- **Two positive complex-balanced concentrations differ by a monomial rescaling.**  This is
the *converse* toric inclusion of Horn and Jackson (1972, Theorem 6.4): the direction of the
rescaling lies in the kernel of the reaction matrix, i.e. it is orthogonal to the
stoichiometric subspace. -/
theorem two_complexBalanced_differ_by_monomial_rescaling (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcbx : N.IsComplexBalanced κ x) (hcbs : N.IsComplexBalanced κ xstar) :
    ∃ u : S → ℝ, u ∈ orthSum N.stoichSubspace ∧ ∀ s, x s = xstar s * Real.exp (u s) := by
  have horth := N.logRatio_orthogonal_of_complexBalanced hwr κ hx hxs hcbx hcbs
  refine ⟨fun s => Real.log (x s) - Real.log (xstar s), horth, ?_⟩
  intro s
  rw [Real.exp_sub, Real.exp_log (hx s), Real.exp_log (hxs s)]
  field_simp [(hxs s).ne']

/-- **Two points of one class with an orthogonal log-ratio coincide** (Birch uniqueness in
the class). -/
theorem eq_of_mem_positiveCompatibilityClass_of_logRatio_orthogonal
    (N : Network S) {x₀ x y : Concentration S} (hx : x ∈ N.positiveCompatibilityClass x₀)
    (hy : y ∈ N.positiveCompatibilityClass x₀)
    (horth : (fun s => Real.log (x s) - Real.log (y s)) ∈ orthSum N.stoichSubspace) :
    x = y := by
  obtain ⟨hxc, hxpos⟩ := hx
  obtain ⟨hyc, hypos⟩ := hy
  have hxy : x - y ∈ N.stoichSubspace := by
    rw [(sub_sub_sub_cancel_right x y x₀).symm]
    exact N.stoichSubspace.sub_mem hxc hyc
  exact birch_uniqueness N.stoichSubspace hxpos hypos hxy fun s hs => (mem_orthSum.mp horth) s hs

/-- **A toric orbit meets a compatibility class in at most one point.**  Two monomial
rescalings of the same complex-balanced equilibrium that lie in the same compatibility class
are equal: the torus action is free and transverse to the classes.  This is the precise content
of the "the complex-balanced set of a class is a union of toric orbits, each of dimension zero
in the class" half of the Horn–Jackson dichotomy. -/
theorem eq_of_same_class_of_monomial_rescaling (N : Network S) {x₀ xstar x y : Concentration S}
    (hxs : xstar.Positive) {u v : S → ℝ} (hu : u ∈ orthSum N.stoichSubspace)
    (hv : v ∈ orthSum N.stoichSubspace) (hx : x ∈ N.positiveCompatibilityClass x₀)
    (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hxu : ∀ s, x s = xstar s * Real.exp (u s))
    (hyv : ∀ s, y s = xstar s * Real.exp (v s)) : x = y := by
  have hsub : u - v ∈ orthSum N.stoichSubspace :=
    (orthSum N.stoichSubspace).sub_mem hu hv
  have hlog : ∀ s, Real.log (x s) - Real.log (y s) = u s - v s := by
    intro s
    rw [hxu s, hyv s, Real.log_mul (hxs s).ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (hxs s).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine N.eq_of_mem_positiveCompatibilityClass_of_logRatio_orthogonal hx hy ?_
  refine mem_orthSum.mpr fun w hw => ?_
  calc ∑ s, (Real.log (x s) - Real.log (y s)) * w s
      = ∑ s, (u s - v s) * w s := Finset.sum_congr rfl fun s _ => by rw [hlog s]
    _ = 0 := (mem_orthSum.mp hsub) w hw

end Network

end CRNT

/-! ## A worked instance: the reversible pair `A ⇌ B` -/

namespace CRNT.Examples.ReversiblePair

open CRNT
open Species

/-- The sum over the two reaction channels of `A ⇌ B`. -/
theorem sum_reactions (g : N.R → ℝ) : (∑ r : N.R, g r) = g Rxn.fwd + g Rxn.bwd := by
  have h : (∑ r : Rxn, g r) = g Rxn.fwd + g Rxn.bwd := by
    rw [show (Finset.univ : Finset Rxn) = {Rxn.fwd, Rxn.bwd} from rfl]
    exact Finset.sum_pair (by decide)
  exact h

/-- **The complex-balanced equilibria of `A ⇌ B` are the monomial rescalings of the
equilibrium.**  Complex balance at the two complexes is the single equation
`k₁ x_B = k₀ x_A`, so the complex-balanced set is the ray through the equilibrium
`(k₁, k₀)`. -/
theorem isComplexBalanced_iff {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    {y : Concentration Species} :
    N.IsComplexBalanced (rates h₀ h₁) y ↔ k₁ * y B = k₀ * y A := by
  constructor
  · intro h
    have hA : Network.inflow N (rates h₀ h₁) y cA = Network.outflow N (rates h₀ h₁) y cA := by
      apply h cA
      rw [complexes_eq]
      simp
    simp only [Network.inflow, Network.outflow] at hA
    rw [sum_reactions, sum_reactions] at hA
    simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, cA, cB,
      prod_univ_species, ite_eq_right (cA_ne_cB.symm)] at hA
    exact hA
  · intro h c hc
    have hc' : c = cA ∨ c = cB := by
      rw [complexes_eq] at hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      exact hc
    rcases hc' with rfl | rfl
    · simp only [Network.inflow, Network.outflow]
      rw [sum_reactions, sum_reactions]
      simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, cA, cB,
        prod_univ_species, ite_eq_right (cA_ne_cB.symm)]
      exact h
    · simp only [Network.inflow, Network.outflow]
      rw [sum_reactions, sum_reactions]
      simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, cA, cB,
        prod_univ_species, ite_eq_right (cA_ne_cB)]
      exact h.symm

/-- **The complex-balanced equilibria of `A ⇌ B` form the monomial-rescaling orbit of the
equilibrium**: they are the points `t · (k₁, k₀)` with `t > 0`, i.e. the images of the
equilibrium under the torus action `x ↦ x · exp u` with `u` in the kernel of the reaction
matrix. -/
theorem exists_smul_equilibrium_of_isComplexBalanced {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    {y : Concentration Species} (hy : y.Positive) (hcb : N.IsComplexBalanced (rates h₀ h₁) y) :
    ∃ t : ℝ, 0 < t ∧ ∀ s, y s = t * equilibrium k₀ k₁ s := by
  have hcond := (isComplexBalanced_iff h₀ h₁).mp hcb
  refine ⟨y A / k₁, div_pos (hy A) h₁, ?_⟩
  intro s
  cases s
  · simp only [equilibrium]
    field_simp
  · have h2 : y B = k₀ * (y A / k₁) := by
      field_simp
      linarith [hcond]
    simp only [equilibrium]
    rw [h2]
    ring

/-- **The complex-balanced equilibrium of `A ⇌ B` is nondegenerate**: the mass-action
Jacobian at the equilibrium is injective on the stoichiometric subspace. -/
theorem equilibrium_isNondegenerate {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    Network.IsNondegenerateAt N (rates h₀ h₁) (equilibrium k₀ k₁) :=
  Network.complexBalanced_isNondegenerate N weaklyReversible (rates h₀ h₁)
    (equilibrium_positive h₀ h₁) (equilibrium_isComplexBalanced h₀ h₁)

/-- **The isolation criterion at work.**  The complex-balanced equilibrium of `A ⇌ B` is the
unique complex-balanced equilibrium in its positive compatibility class. -/
theorem equilibrium_unique_complexBalanced_in_class {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    {y : Concentration Species} (hy : y ∈ N.positiveCompatibilityClass (equilibrium k₀ k₁))
    (hcb : N.IsComplexBalanced (rates h₀ h₁) y) : y = equilibrium k₀ k₁ := by
  obtain ⟨_, huniq⟩ :=
    Network.unique_complexBalanced_of_nondegenerate N (rates h₀ h₁) (equilibrium k₀ k₁)
      (equilibrium_positive h₀ h₁) (equilibrium_isComplexBalanced h₀ h₁)
      (equilibrium_isNondegenerate h₀ h₁)
  exact huniq y hy hcb

end CRNT.Examples.ReversiblePair

#print axioms CRNT.Network.unique_complexBalanced_of_nondegenerate
#print axioms CRNT.Network.unique_complexBalanced_in_positiveClass
#print axioms CRNT.Network.exists_unique_isComplexBalanced_in_positiveClass
#print axioms CRNT.Network.isNondegenerate_iff_injective_reducedJacobian
#print axioms CRNT.Network.isNondegenerate_iff_strict_dissipation
#print axioms CRNT.Network.complexBalanced_isNondegenerate
#print axioms CRNT.Network.two_complexBalanced_differ_by_monomial_rescaling
#print axioms CRNT.Network.isComplexBalanced_of_monomial_rescaling
#print axioms CRNT.Network.eq_of_same_class_of_monomial_rescaling
#print axioms CRNT.Network.mem_orthSum_stoichSubspace_iff
#print axioms CRNT.Examples.ReversiblePair.equilibrium_unique_complexBalanced_in_class
#print axioms CRNT.Examples.ReversiblePair.isComplexBalanced_iff
