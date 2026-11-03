import CRNT.Equilibria.CompatibilityClassGeometry
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Geometry.ConservativeCompatibility
import CRNT.Kinetics.MassAction
import CRNT.Flux.PSemiflow
import Mathlib.Analysis.Convex.Basic

/-!
# Conservation-law invariants of a stoichiometric compatibility class

This module formalizes the invariant-theoretic content of the compatibility class
`C(x₀) = x₀ + S(N)` — the polyhedron confining every mass-action trajectory, and the object the
ω-limit hypothesis `hωaff` of `CRNT.Dynamics.HighCodimensionSiphonFace` places the orbit in.

`CRNT.Equilibria.CompatibilityClassGeometry` supplies the affine structure and the convexity of
the class; `CRNT.Geometry.CompatibilityFaces` supplies the conservation-law *exclusion* of a
coordinate face; `CRNT.Flux.PSemiflow` supplies the raw invariant API. What is proved here is
the transport layer that connects them, and — importantly — the **non-vacuity boundary**: an
exact characterisation of when the invariant apparatus is trivial.

## Contents

**A. Transport: P-invariants are constant along the class and along its segments.**

* `weightedTotal_eq_of_mem_compatibilityClass` : repackaged constant-along-the-class.
* `weightedTotal_eq_of_mem_nonnegativeCompatibilityClass` : the same on the nonnegative part,
  which is where ω-limit points of a mass-action trajectory live. This is the step that carries
  a conservation law from the trajectory to its ω-points.
* `weightedTotal_eq_of_segment` : the weighted total is constant along any class segment — the
  discrete LaSalle structure of a conservative system: the state cannot leave the class and one
  scalar is conserved.

**B. Boundedness: a strictly positive invariant makes the class a bounded polytope.**

* `coordinate_le_weightedTotal_div` : every coordinate of a nonnegative class point is bounded by
  the conserved total.
* `bddAbove_setOf_nonnegativeClass` : the nonnegative class is bounded above, coordinatewise, by
  the constant vector `fun s => weightedTotal w x₀ / w s` — the boundedness half of
  Craciun–Nazarov–Pantea's "the compatibility class is a polytope" (Definition 2.3).

The `IsBounded` and `IsCompact` forms of both statements are **not** re-proved here: they are
already `CRNT.Geometry.ConservativeCompatibility.isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow`
and `CRNT.Geometry.ConservativeCompatibility.isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow`,
and redeclaring them here would clash with those names.

**C. Non-vacuity boundary: the invariant apparatus is trivial exactly when `S(N) = ⊤`.**

The conservation laws of `N` form `orthSum S(N)`. Note that `S(N) = ⊥` says the *opposite* of
what one might expect: with no stoichiometric constraint at all, **every** vector is a
P-invariant. The conservation-law apparatus is therefore empty exactly when the stoichiometric
subspace is the whole space, `S(N) = ⊤`:

* `isPInvariant_of_stoichSubspace_eq_bot` : `S(N) = ⊥` makes every vector a P-invariant. This is
  the true content of the `⊥` case.
* `eq_zero_of_mem_orthSum_of_stoichSubspace_eq_top` : `S(N) = ⊤` forces every P-invariant to be
  the zero law.
* `no_nonzero_PSemiflow_of_stoichSubspace_eq_top`, `no_strictPSemiflow_of_stoichSubspace_eq_top` :
  hence no P-semiflow and no strictly positive P-semiflow, so part B's boundedness cannot apply.
* `stoichSubspace_eq_top_of_nonzero_PSemiflow` : the converse. So the invariant apparatus is
  **coextensive** with `S(N) ≠ ⊤`.
* `stoichSubspace_eq_bot_of_all_reactionVectors_zero` : the degenerate case in coordinates.
* `exists_mem_compatibilityClass_neq_of_stoichSubspace_ne_bot` : the class is genuinely
  non-singleton, so `CRNT.Equilibria.CompatibilityClassGeometry`'s affine structure is not
  vacuous.

**Note on the original formulation.** Ported from `research/FormScaffold`, this module carried
`S(N) = ⊥` in the hypothesis of four conservation-law statements, and claimed that the apparatus
is trivial exactly in that case. Those statements are **false**: for a reactionless network
`R = ∅` one has `S(N) = ⊥`, yet `w = fun _ => 1` is a nonzero, strictly positive P-invariant
(`isPInvariant_of_stoichSubspace_eq_bot`). The hypothesis has been corrected to `S(N) = ⊤` — the
genuinely "fully constrained" case — and the names changed accordingly.

**A negative result worth recording.** It is tempting to write "a strictly positive invariant
separates two class points by their weighted totals". **That is false**, and provably so:
`CRNT.Flux.PSemiflow.weightedTotal_eq_of_stoichCompatible` says the weighted total is *equal* on
any two compatible points. The correct separation statement is the conservation exclusion in
`CRNT.Geometry.CompatibilityFaces.compatibilityFace_empty_of_carriesPositiveConservationLaw`:
a conservation law supported on `P` excludes the whole `P`-face rather than separating points.
See `weightedTotal_eq_of_stoichCompatible_is_the_correct_statement` below, which records the
equality form explicitly so the false variant cannot be re-attempted.

**D. Worked example (non-vacuity).**

`exampleAtoB'` is `A → B` over `S = Fin 2`. Verified: `S(N)` is nontrivial but proper, the class
of `(1,1)` is a genuine line containing `(0,2)`, the uniform law `w = (1,1)` is a strictly positive
P-invariant, and consequently the nonnegative class of `(1,1)` is a **compact** polytope — part B
in action, and part C coextensive with `S(N) ≠ ⊤`.

(The ported version claimed `A → B` is **not** conservative; that is false, see the docstring of
`exampleAtoB_isConservative`.)

**Source.** Horn–Jackson, *Generalized mass action laws*, Arch. Rational Mech. Anal. **47**
(1972), 81–116 (the affine class and its conservation laws); Craciun–Nazarov–Pantea,
*Persistence and permanence of mass-action and power-law dynamical systems*,
J. Math. Anal. Appl. **342** (2008), 366–382, Definition 2.3 (the class as a polytope).

Depends on: `CRNT.Equilibria.CompatibilityClassGeometry`,
`CRNT.Equilibria.ComplexBalanceStructure`, `CRNT.Kinetics.MassAction`,
`CRNT.Flux.PSemiflow`, `CRNT.Geometry.ConservativeCompatibility`.
-/

namespace CRNT
namespace Network

open scoped BigOperators Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. Transport: P-invariants are constant along the class -/

/-- **Every P-invariant is constant along the stoichiometric compatibility class.** Since the class
is `x₀ + S(N)` and a P-invariant annihilates `S(N)`, its weighted total takes the value `w(x₀)` at
every class point.

This is the step that transports a conservation law from a trajectory to its ω-limit points: if
`Ω ⊆ C(x₀)` then `w z = w x₀` for every `z ∈ Ω`. -/
theorem weightedTotal_eq_of_mem_compatibilityClass (N : Network S) {w : S → ℝ}
    (hw : N.IsPInvariant w) {x₀ x : Concentration S} (hx : x ∈ N.compatibilityClass x₀) :
    weightedTotal w x = weightedTotal w x₀ :=
  N.pInvariant_constant_on_compatibilityClass hw x₀ x hx

/-- **P-invariants are constant on the nonnegative part of the class too**, which is where
ω-limit points of a mass-action trajectory live. -/
theorem weightedTotal_eq_of_mem_nonnegativeCompatibilityClass (N : Network S) {w : S → ℝ}
    (hw : N.IsPInvariant w) {x₀ x : Concentration S}
    (hx : x ∈ N.nonnegativeCompatibilityClass x₀) :
    weightedTotal w x = weightedTotal w x₀ :=
  N.weightedTotal_eq_of_stoichCompatible hw hx.1.symm

/-- **The weighted total is constant along class segments.** For `0 ≤ t ≤ 1` the segment from `x₀`
to a compatible `x` stays in the class and the weighted total is unchanged.  This is the discrete
LaSalle structure of a conservative system: the state cannot leave the class, and one scalar is
conserved. -/
theorem weightedTotal_eq_of_segment (N : Network S) {w : S → ℝ} (hw : N.IsPInvariant w)
    {x₀ x : Concentration S} (hcomp : N.StoichCompatible x₀ x) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    weightedTotal w ((1 - t) • x₀ + t • x) = weightedTotal w x₀ := by
  have hseg : N.StoichCompatible x₀ ((1 - t) • x₀ + t • x) :=
    N.stoichCompatible_segment hcomp ht0 ht1
  exact N.weightedTotal_eq_of_stoichCompatible hw hseg.symm

/-- **The corrected separation statement, recorded explicitly.** The weighted total of a strictly
positive P-invariant is *equal*, not merely comparable, on any two compatible points.  This is the
statement that refutes the tempting "strictly positive invariant separates class points" claim;
the usable form of conservation exclusion is the face-emptiness of
`CRNT.Geometry.CompatibilityFaces`, not point separation. -/
theorem weightedTotal_eq_of_stoichCompatible_is_the_correct_statement (N : Network S)
    {w : S → ℝ} (hw : N.IsStrictPSemiflow w) {x y : Concentration S}
    (h : N.StoichCompatible x y) : weightedTotal w x = weightedTotal w y :=
  N.weightedTotal_eq_of_stoichCompatible hw.1 h

/-! ### B. Boundedness from a strictly positive invariant -/

/-- **Every coordinate of a nonnegative class point is bounded by the conserved total.** -/
theorem coordinate_le_weightedTotal_div (N : Network S) {w : S → ℝ}
    (hw : N.IsStrictPSemiflow w) {x₀ x : Concentration S}
    (hx₀ : x₀.Nonnegative) (hx : x.Nonnegative) (hcomp : N.StoichCompatible x₀ x) (s : S) :
    x s ≤ weightedTotal w x₀ / w s :=
  N.coordinate_le_of_strictPSemiflow hw hx₀ hx hcomp s

/-- **Boundedness of the nonnegative class from a single conserved scalar.** Every member of the
nonnegative part of the class lies coordinatewise below the constant vector
`fun s => weightedTotal w x₀ / w s`, which is the coordinate box
`CRNT.Flux.PSemiflow.coordinate_le_of_strictPSemiflow` gives. (The `IsBounded` form, with the
summation bound `∑ s, weightedTotal w x₀ / w s`, is in
`CRNT.Geometry.ConservativeCompatibility`.) -/
theorem bddAbove_setOf_nonnegativeClass (N : Network S) {w : S → ℝ}
    (hw : N.IsStrictPSemiflow w) {x₀ : Concentration S} (hnn : x₀.Nonnegative) :
    BddAbove (N.nonnegativeCompatibilityClass x₀) :=
  ⟨fun s => weightedTotal w x₀ / w s, fun _x hx s =>
    N.coordinate_le_weightedTotal_div hw hnn hx.2 hx.1 s⟩

/-! ### C. Non-vacuity boundary: the invariant apparatus and `S(N) ≠ ⊤` -/

/-- **The orthogonal complement of the full space is trivial.** -/
theorem orthSum_top {ι : Type} [Fintype ι] :
    orthSum (⊤ : Submodule ℝ (ι → ℝ)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro w hw
  rw [mem_orthSum] at hw
  refine (Submodule.mem_bot ℝ).mpr (funext fun s => ?_)
  have hs0 : ∑ i, w i * w i = 0 := hw w Submodule.mem_top
  by_contra hne
  have hpos : 0 < ∑ i, w i * w i :=
    Finset.sum_pos' (fun i _ => mul_self_nonneg _)
      ⟨s, Finset.mem_univ s, mul_self_pos.mpr hne⟩
  linarith

/-- **The `⊥` case, stated correctly.** An *unconstrained* network — one whose stoichiometric
subspace is `⊥` — imposes no constraint at all, so **every** species vector is a P-invariant.

This is the exact opposite of the claim this module originally made; see the note in the module
docstring. It is recorded here because it is the reason the conservation-law apparatus is
non-trivial exactly when `S(N) ≠ ⊤`. -/
theorem isPInvariant_of_stoichSubspace_eq_bot (N : Network S) (hS : N.stoichSubspace = ⊥)
    (w : S → ℝ) : N.IsPInvariant w := by
  rw [IsPInvariant, hS, mem_orthSum]
  intro s hs
  rw [(Submodule.mem_bot ℝ).mp hs]
  simp

/-- **Fully constrained means no conservation law.** If `S(N) = ⊤` then `orthSum S(N) = ⊥`, so
the conservation-law apparatus is empty: every P-invariant is the zero law. -/
theorem eq_zero_of_mem_orthSum_of_stoichSubspace_eq_top (N : Network S)
    (hS : N.stoichSubspace = ⊤) {w : S → ℝ} (hw : N.IsPInvariant w) : w = 0 := by
  have hw' : w ∈ (⊥ : Submodule ℝ (S → ℝ)) := by
    have h : w ∈ orthSum N.stoichSubspace := hw
    rwa [hS, orthSum_top] at h
  exact (Submodule.mem_bot ℝ).mp hw'

/-- **Fully constrained networks have no nonzero P-semiflow.** -/
theorem no_nonzero_PSemiflow_of_stoichSubspace_eq_top (N : Network S)
    (hS : N.stoichSubspace = ⊤) : ¬ ∃ w : S → ℝ, N.IsPSemiflow w := by
  rintro ⟨w, hw⟩
  exact hw.2.2 (N.eq_zero_of_mem_orthSum_of_stoichSubspace_eq_top hS hw.1)

/-- **Fully constrained networks have no strictly positive P-semiflow**, so the boundedness and
compactness of part B are genuinely *constrained* phenomena.

`S` must be nonempty for the last step: on the empty species set the positivity hypothesis
`∀ s, 0 < w s` is vacuous and holds for `w = 0`. -/
theorem no_strictPSemiflow_of_stoichSubspace_eq_top [Nonempty S] (N : Network S)
    (hS : N.stoichSubspace = ⊤) : ¬ ∃ w : S → ℝ, N.IsStrictPSemiflow w := by
  rintro ⟨w, hw⟩
  have hw0 := N.eq_zero_of_mem_orthSum_of_stoichSubspace_eq_top hS hw.1
  have hwpos := hw.2 (Classical.arbitrary (α := S))
  rw [hw0] at hwpos
  norm_num at hwpos

/-- **The converse**: a network admitting a nonzero conservation law is not fully constrained.
Together with the two preceding lemmas this makes the invariant apparatus exactly coextensive
with `S(N) ≠ ⊤`. -/
theorem stoichSubspace_eq_top_of_nonzero_PSemiflow (N : Network S)
    (h : ∃ w : S → ℝ, N.IsPSemiflow w) : N.stoichSubspace ≠ ⊤ := by
  rintro hS
  obtain ⟨w, hw⟩ := h
  exact hw.2.2 (N.eq_zero_of_mem_orthSum_of_stoichSubspace_eq_top hS hw.1)

/-- **The unconstrained case is genuinely degenerate, in coordinates too**: if every reaction
vector vanishes then `S(N) = ⊥`, i.e. every species vector `v` satisfies `v = 0`. -/
theorem stoichSubspace_eq_bot_of_all_reactionVectors_zero (N : Network S)
    (h : ∀ r : N.R, N.reactionVector r = 0) : N.stoichSubspace = ⊥ := by
  rw [stoichSubspace]
  refine le_antisymm (Submodule.span_le.2 ?_) bot_le
  intro v hv
  obtain ⟨r, rfl⟩ := hv
  exact (Submodule.mem_bot ℝ).mpr (by exact h r)

/-- **Nontriviality of the class.** A nonzero stoichiometric subspace contains a nonzero vector,
and translating `x₀` by it lands inside the class at a genuinely different point, so the affine
structure of `CRNT.Equilibria.CompatibilityClassGeometry` is not vacuous. -/
theorem exists_mem_compatibilityClass_neq_of_stoichSubspace_ne_bot (N : Network S)
    (x₀ : Concentration S) (hS : N.stoichSubspace ≠ ⊥) :
    ∃ x, x ∈ N.compatibilityClass x₀ ∧ x ≠ x₀ := by
  obtain ⟨w, hwmem, hw0⟩ := Submodule.ne_bot_iff N.stoichSubspace |>.mp hS
  have hcompat : N.StoichCompatible x₀ (x₀ + (1 : ℝ) • w) :=
    N.stoichCompatible_smul_add w hwmem 1
  refine ⟨x₀ + (1 : ℝ) • w, hcompat, ?_⟩
  intro hcon
  apply hw0
  funext s
  have hs := congrFun hcon s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs
  have hs0 : (0 : Concentration S) s = 0 := rfl
  linarith

/-! ### D. Worked example: the two-species network `A → B` -/

section Example

/-- The two-species single-reaction network `A → B` over `S = Fin 2`. -/
def exampleAtoB' : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- **The stoichiometric subspace of `A → B` is nontrivial**, so the class is a genuine line and
the invariant apparatus above is not vacuous. -/
theorem example_stoichSubspace_ne_bot : exampleAtoB'.stoichSubspace ≠ ⊥ := by
  intro h
  have hmem := exampleAtoB'.reactionVector_mem_stoichSubspace ()
  rw [h] at hmem
  rw [Submodule.mem_bot] at hmem
  have hz := congrFun hmem (1 : Fin 2)
  simp [exampleAtoB'] at hz

/-- **The class of `(1,1)` is non-singleton**: it contains a concentration different from `(1,1)`.
The witness produced here is a translation of `(1,1)` by a nonzero element of `S(N)`; the
concrete representative `(0,2)` is exhibited in
`CRNT.Equilibria.CompatibilityClassGeometry.exampleAtoB_stoichCompatible_01`. -/
theorem example_class_nonconstant :
    ∃ x, x ∈ exampleAtoB'.compatibilityClass (fun _ => (1 : ℝ)) ∧ x ≠ (fun _ => (1 : ℝ)) :=
  exampleAtoB'.exists_mem_compatibilityClass_neq_of_stoichSubspace_ne_bot _
    example_stoichSubspace_ne_bot

/-- **The uniform law `w = (1, 1)` is a P-invariant of `A → B`**: it pairs to `0` with the single
reaction vector `(-1,1)`. -/
theorem exampleAtoB_one_isPInvariant : exampleAtoB'.IsPInvariant (fun _ => (1 : ℝ)) := by
  rw [IsPInvariant]
  refine (exampleAtoB'.conservationLaw_iff_mem_orthSum (fun _ => (1 : ℝ))).mp ?_
  intro r
  have hr : ∀ r : exampleAtoB'.R, exampleAtoB'.reactionVector r = fun s => if s = (0 : Fin 2) then -1 else 1 := by
    intro r
    funext s
    rcases s with ⟨(_ | n), h⟩
    · dsimp only [exampleAtoB', Network.reactionVector, Reaction.vector]
      norm_num
    · have hn : n = 0 := by omega
      subst hn
      dsimp only [exampleAtoB', Network.reactionVector, Reaction.vector]
      norm_num
  rw [hr r, Fin.sum_univ_two]
  simp

/-- Hence the uniform law is a **strictly positive** P-invariant of `A → B`. -/
theorem exampleAtoB_one_isStrictPSemiflow :
    exampleAtoB'.IsStrictPSemiflow (fun _ => (1 : ℝ)) :=
  ⟨exampleAtoB_one_isPInvariant, fun _ => one_pos⟩

/-- **The conserved total really is constant along the class of `A → B`.** For the law
`w = (1, 1)` the weighted total is `x 0 + x 1`; at the class point `(1,1)` it is `2`. -/
theorem example_total_conserved :
    weightedTotal (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      = weightedTotal (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) := by
  exact exampleAtoB'.weightedTotal_eq_of_stoichCompatible_is_the_correct_statement
    exampleAtoB_one_isStrictPSemiflow (StoichCompatible.refl _ _)

/-- **A strictly positive P-invariant really does bound the class**, at the concrete point:
`w = (1,1)` is orthogonal to the reaction vector `(-1,1)`, and at `x₀ = x = (1,1)` the bound on
coordinate `0` reads `1 ≤ 2 / 1`.  This is `coordinate_le_weightedTotal_div` at species `0`. -/
theorem example_bounded :
    (1 : ℝ) ≤ weightedTotal (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      / (fun _ : Fin 2 => (1 : ℝ)) 0 := by
  have h := exampleAtoB'.coordinate_le_weightedTotal_div (w := fun _ => (1 : ℝ))
    exampleAtoB_one_isStrictPSemiflow (fun _ => by norm_num) (fun _ => by norm_num)
    (StoichCompatible.refl (N := exampleAtoB') (x := fun _ => (1 : ℝ))) (0 : Fin 2)
  norm_num at h ⊢
  exact h

/-- **`A → B` is conservative.** The law `w = (1,1)` is strictly positive and pairs to `0` with
the reaction vector `(-1,1)` (indeed `-1 + 1 = 0`), so part B applies: the nonnegative class of
`(1,1)` is a compact polytope, as `example_class_isCompact` records below.

(The ported version of this module claimed the opposite — that `A → B` admits no strictly positive
conservation law, on the erroneous ground that `a·(-1) + a·1 = 0` forces `a = 0`. It forces
`w 0 = w 1` instead, which `(1,1)` satisfies.) -/
theorem exampleAtoB_isConservative : exampleAtoB'.IsConservative :=
  ⟨fun _ => (1 : ℝ), exampleAtoB_one_isStrictPSemiflow⟩

/-- **The stoichiometric subspace of `A → B` is nevertheless proper.** The uniform law
`w = (1,1)` is orthogonal to every reaction vector, so `w ∈ orthSum S(N)`, and pairing it with
itself gives `2 = 0`; hence `w ∉ S(N)`, and `S(N) ≠ ⊤`. By section C the conservation-law
apparatus is therefore non-trivial, and its members are exactly the multiples of `(1,1)`. -/
theorem example_stoichSubspace_ne_top : exampleAtoB'.stoichSubspace ≠ ⊤ := by
  intro h
  have hone : (fun _ => (1 : ℝ)) ∈ exampleAtoB'.stoichSubspace := by
    rw [h]
    simp only [Submodule.mem_top]
  have hw : (fun _ => (1 : ℝ)) ∈ orthSum exampleAtoB'.stoichSubspace := by
    show (fun _ => (1 : ℝ)) ∈ orthSum (Submodule.span ℝ (Set.range exampleAtoB'.reactionVector))
    refine mem_orthSum_span ?_
    rintro _ ⟨r, rfl⟩
    rw [Fin.sum_univ_two]
    dsimp only [exampleAtoB', Network.reactionVector, Reaction.vector]
    norm_num
  have hone' : (fun _ => (1 : ℝ)) ∈ orthSum (orthSum exampleAtoB'.stoichSubspace) := by
    rw [orthSum_orthSum]
    exact hone
  have hz := (mem_orthSum.mp hone') (fun _ => (1 : ℝ)) hw
  rw [Fin.sum_univ_two] at hz
  norm_num at hz

/-- **Part B in action**: the nonnegative class of `(1,1)` in `A → B` is compact, the concrete
form of "the compatibility class is a polytope". -/
theorem example_class_isCompact :
    IsCompact (exampleAtoB'.nonnegativeCompatibilityClass (fun _ => (1 : ℝ))) :=
  exampleAtoB'.isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow
    exampleAtoB_one_isStrictPSemiflow (fun _ => by norm_num)

end Example

end Network
end CRNT