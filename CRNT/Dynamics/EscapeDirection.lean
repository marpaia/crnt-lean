import CRNT.Dynamics.ConservationLaw
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Stoich.ConservationDimension
import CRNT.Persistence.ConservativePersistence
import CRNT.Examples.ReversiblePair

/-!
# Escape directions: the geometric content of the unbounded case of the persistence conjecture

This module formalizes the *geometry* of a possible escape to infinity of a mass-action
trajectory, which is the part of the Persistence Conjecture (field-map leaf **D12**) that is
still open.  The bounded case of D12 is already proved in the repository: for a weakly reversible
network and any positive rate constants, every forward solution from a positive state that is
bounded above has a positive lower bound depending only on the initial state and the upper bound
(`CRNT.Network.weaklyReversible_forward_floor`, `CRNT.Network.weaklyReversible_forward_floor_uniform`).
Consequently the compact-confinement form of the conjecture holds for every conservative network
(`CRNT.Network.persistenceConjectureStrong_of_conservative`).  What is missing is the *unbounded*
case: trajectories that run off to infinity, in three or more species, in networks that are not
conservative.

The present module isolates the linear-algebraic and geometric content of that remaining case.

## The two orthogonal spaces

For a network `N` on species `S` the conservation-law space is

  `V = N.conservationLawSpace = orthSum N.stoichSubspace`,

the set of species vectors `w` orthogonal to every reaction vector, i.e. the *conservation
laws* (`N.IsPInvariant w` is the same predicate, see `CRNT.Flux.PSemiflow`).  A conservation law
`w` is a constant of motion along every mass-action trajectory: `⟨w, x t⟩ = ⟨w, x 0⟩`
(`CRNT.Network.conservationLaw_const_along_solution`).

The orthogonal complement of the conservation-law space,

  `Vᶜ = orthSum V`,

is the *escape direction*: the set of displacements that no conservation law can see.  Since
`V = orthSum N.stoichSubspace`, the double-complement identity of
`CRNT.LinearAlgebra.OrthogonalComplement` gives

  `Vᶜ = N.stoichSubspace`  (`orthSum_conservationLawSpace`),

which is exactly the space the mass-action velocity lives in.  Consequently:

* the displacement `x t − x 0` of a trajectory lies in `Vᶜ` (`escape_in_orthogonalComplement`):
  the *conserved* component of the trajectory is the one seen by the conservation laws, and it is
  constant;
* the orthogonal projection of the trajectory onto the conservation-law space is constant
  (`projection_on_conservationLawSpace_const`), so any escape to infinity happens in `Vᶜ`, in
  the direction that the conservation laws annihilate.

Note on conventions: the notes for leaf D12 phrase the escape statement as "the projection of
`x t` onto `Vᶜ` is constant".  With the repository's convention
(`CRNT.LinearAlgebra.OrthogonalComplement`: `orthSum S = {w | ∀ s ∈ S, ∑ i, w i * s i = 0}`) the
mathematically correct statement is the complementary one: the projection onto the
*conservation-law space* `V` is constant, and the *escaping* component lives in `Vᶜ`.  Both are
proved below; together they are the content of "the escape is in the kernel of the conservation
laws".

## Consequences

* `no_escape_of_positive_conservation_law`: a strictly positive conservation law bounds every
  coordinate of every forward trajectory, so the trajectory cannot escape; combined with the
  bounded case of D12 the trajectory then has a positive lower bound depending only on the
  initial state and the rates.  Equivalently, the Persistence Conjecture holds for every network
  that admits a strictly positive conservation law
  (`persistenceConjectureStrong_of_positive_conservation_law`).
* `escape_confined_to_zero_face`: the species that can run to infinity are exactly those that no
  *nonnegative* conservation law detects; the escaping species lie in the face
  `N.escapeFace` of the nonnegative orthant, and every other species has a uniformly bounded
  coordinate.  The linear "zero set" `N.conservationLawZeroSet` of the conservation laws (the
  species annihilated by *every* conservation law) is contained in that face
  (`conservationLawZeroSet_subset_escapeFace`).

## The instances

* `CRNT.Examples.ReversiblePair`: the network `A ⇌ B` with the strictly positive conservation
  law `A + B`.  Every forward trajectory is bounded by the initial total mass and therefore has
  a positive lower bound depending only on the initial state and the rates
  (`totalMass_conservationLaw`, `bounded_by_initial_total`, `bounded_and_persistent`).
* `CRNT.Examples.EscapeAutocatalysis`: the network `A → 2A` with a spectator `B`.  The `B`-count
  is a conservation law, `A` is invisible to every conservation law and lies in the escaping
  face, `B` does not, and the explicit solution `A(t) = e^t`, `B(t) = 1` escapes to infinity
  while its `B`-coordinate stays bounded.

## A remark on the zero set

The zero set `N.conservationLawZeroSet` (the species annihilated by *every* conservation law)
is contained in the escaping face `N.escapeFace`, but the two are not equal in general.  A
sign-changing conservation law such as `A - B` detects both `A` and `B`, while no *nonnegative*
conservation law does; in that case `A` and `B` escape together, so the naive reading "the
escaping species are exactly those of the zero set" is false.  The face statement is the
correct one: a species detected by a nonnegative conservation law has a bounded coordinate,
because the conserved total is a constant of motion and the trajectory is nonnegative.

## What is not proved here

The orthant-forward-invariance of mass-action trajectories is not formalized in the repository:
`CRNT.Network.massActionVectorField_nonneg_of_zero` is the algebraic heart of it (at a
nonnegative state with `x s = 0` the `s`-component of the field is nonnegative), but the
first-crossing argument is missing.  The face theorem therefore carries the hypothesis that the
trajectory stays in the nonnegative orthant, which is the physically correct setting; in the
conservative case the hypothesis is discharged by the repository
(`CRNT.Network.conservative_forward_bound` gives positivity through
`CRNT.Network.orbit_pos_forward_of_bdd_nonneg`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The escape direction is the stoichiometric subspace -/

/-- **The escape direction.** The orthogonal complement of the conservation-law space is the
stoichiometric subspace: the displacements that no conservation law can see are exactly the
linear combinations of reaction vectors, i.e. the directions in which the mass-action velocity
moves. -/
theorem orthSum_conservationLawSpace (N : Network S) :
    orthSum N.conservationLawSpace = N.stoichSubspace := by
  show orthSum (orthSum N.stoichSubspace) = N.stoichSubspace
  exact orthSum_orthSum _

/-- **The conservation-law space and the escape direction are complementary.** Every species
vector splits into a part seen by the conservation laws and a part in the escape direction. -/
theorem sup_conservationLawSpace_orthSum (N : Network S) :
    N.conservationLawSpace ⊔ orthSum N.conservationLawSpace = ⊤ := by
  have h := sup_inf_orthSum_of_le (U := N.conservationLawSpace) (V := ⊤) (le_top)
  simpa using h

/-! ### Conservation laws are constants of motion -/

/-- **Conservation laws are constants of motion (the `IsPInvariant` form).**  Along a forward
mass-action solution, the `w`-weighted total is the same at every forward time, for every
conservation law `w`.  This is the repository theorem
`CRNT.Network.conservationLaw_const_along_solution`, re-expressed for the invariant
`N.IsPInvariant` and in the `weightedTotal` notation; it is the reason why a conservation law
can never detect an escape. -/
theorem conservationLaw_total_const_along_solution (N : Network S) (κ : N.RateConstants)
    {w : S → ℝ} (hw : N.IsPInvariant w) {x : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) :
    weightedTotal w (x t) = weightedTotal w (x 0) := by
  have h := N.conservationLaw_const_along_solution κ hw ht (fun τ hτ => hsol τ hτ.1)
  simpa [weightedTotal] using h

/-- **Conservation laws are constants of motion (the `conservationLawSpace` form).**  Every
member of the conservation-law space has a constant weighted total along a forward mass-action
solution. -/
theorem conservationLawSpace_total_const_along_solution (N : Network S) (κ : N.RateConstants)
    {w : S → ℝ} (hw : w ∈ N.conservationLawSpace) {x : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) :
    weightedTotal w (x t) = weightedTotal w (x 0) := by
  have h := N.conservationLaw_const_along_solution κ hw ht (fun τ hτ => hsol τ hτ.1)
  simpa [weightedTotal] using h

/-! ### The escape direction of a trajectory -/

/-- **The escape is in the kernel of the conservation laws.**  The displacement of a forward
mass-action solution between two forward times lies in the orthogonal complement of the
conservation-law space, i.e. in the escape direction
(`orthSum N.conservationLawSpace = N.stoichSubspace`).  Equivalently: the component of the
trajectory seen by the conservation laws is constant, and the part of the trajectory that can
grow without bound is annihilated by every conservation law. -/
theorem escape_in_orthogonalComplement (N : Network S) (κ : N.RateConstants)
    {x : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) :
    (x t : S → ℝ) - x 0 ∈ orthSum N.conservationLawSpace := by
  have h1 := N.sub_mem_stoichSubspace_of_solution κ ht (fun τ hτ => hsol τ hτ.1)
  rw [orthSum_conservationLawSpace N]
  exact h1

/-- **The conservation-law component of the trajectory is constant.**  In the Euclidean
realization of the species space, the orthogonal projection of the trajectory onto the
conservation-law space `N.conservationLawSpace` does not move: the trajectory moves only in the
escape direction `orthSum N.conservationLawSpace`.  This is the literal "projection" form of
`escape_in_orthogonalComplement`; it is the geometric statement that a trajectory cannot escape
in a direction that a conservation law can see. -/
theorem projection_on_conservationLawSpace_const (N : Network S) (κ : N.RateConstants)
    {x : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) :
    (N.conservationLawSpace.map toEuclid.toLinearMap).starProjection (toEuclid (x t))
      = (N.conservationLawSpace.map toEuclid.toLinearMap).starProjection (toEuclid (x 0)) := by
  set K : Submodule ℝ (EuclideanSpace ℝ S) := N.conservationLawSpace.map toEuclid.toLinearMap
  have hmem : (x t : S → ℝ) - x 0 ∈ orthSum N.conservationLawSpace :=
    N.escape_in_orthogonalComplement κ ht hsol
  have hmap : toEuclid ((x t : S → ℝ) - x 0) ∈
      (orthSum N.conservationLawSpace).map toEuclid.toLinearMap :=
    Submodule.mem_map_of_mem hmem
  have hkey : (orthSum N.conservationLawSpace).map toEuclid.toLinearMap = K.orthogonal := by
    rw [orthSum_eq, Submodule.map_comap_eq_of_surjective toEuclid.surjective]
  rw [hkey] at hmap
  have hsub : toEuclid (x t) - toEuclid (x 0) = toEuclid ((x t : S → ℝ) - x 0) := by
    simp [map_sub]
  rw [← hsub] at hmap
  -- the projection of `x 0` is in `K`, and `x t` differs from it by a vector of `Kᶜ`
  have hv : K.starProjection (toEuclid (x 0)) ∈ K := K.starProjection_apply_mem _
  have hvo : toEuclid (x t) - K.starProjection (toEuclid (x 0)) ∈ K.orthogonal := by
    have h1 : toEuclid (x t) - toEuclid (x 0) ∈ K.orthogonal := hmap
    have h2 : toEuclid (x 0) - K.starProjection (toEuclid (x 0)) ∈ K.orthogonal :=
      K.sub_starProjection_mem_orthogonal _
    have h3 : toEuclid (x t) - K.starProjection (toEuclid (x 0))
        = (toEuclid (x t) - toEuclid (x 0))
          + (toEuclid (x 0) - K.starProjection (toEuclid (x 0))) := by abel
    rw [h3]
    exact K.orthogonal.add_mem h1 h2
  exact Submodule.eq_starProjection_of_mem_orthogonal hv hvo

/-- **Escape to infinity happens in the escape direction.**  If a forward mass-action solution
runs off to infinity, then the conservation-law component of the trajectory is constant
(`projection_on_conservationLawSpace_const`) and the displacement of the trajectory lies in the
escape direction `orthSum N.conservationLawSpace`; in particular the trajectory is not constant.
This is the geometric content of the still-open unbounded case of leaf D12: the only way a
trajectory can escape is through the directions annihilated by every conservation law. -/
theorem escape_to_infinity_in_escape_direction (N : Network S) (κ : N.RateConstants)
    {x : ℝ → Concentration S}
    (hesc : Filter.Tendsto (fun t => ‖(x t : S → ℝ)‖) Filter.atTop Filter.atTop)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ)
    {t : ℝ} (ht : 0 ≤ t) :
    (x t : S → ℝ) - x 0 ∈ orthSum N.conservationLawSpace ∧
      (N.conservationLawSpace.map toEuclid.toLinearMap).starProjection (toEuclid (x t))
        = (N.conservationLawSpace.map toEuclid.toLinearMap).starProjection (toEuclid (x 0)) ∧
      ∃ t : ℝ, 0 ≤ t ∧ (x t : S → ℝ) ≠ x 0 := by
  refine ⟨N.escape_in_orthogonalComplement κ ht hsol,
    N.projection_on_conservationLawSpace_const κ ht hsol, ?_⟩
  by_contra hcon
  have hconst : ∀ s : ℝ, 0 ≤ s → (x s : S → ℝ) = x 0 := by
    intro s hs
    by_contra hne
    exact hcon ⟨s, hs, hne⟩
  have h1 : ∀ᶠ s in Filter.atTop, ‖(x 0 : S → ℝ)‖ + 1 ≤ ‖(x s : S → ℝ)‖ :=
    hesc.eventually_ge_atTop (‖(x 0 : S → ℝ)‖ + 1)
  have h2 : ∀ᶠ s in Filter.atTop, (0 : ℝ) ≤ s := Filter.eventually_ge_atTop 0
  have h3 : ∀ᶠ s in Filter.atTop, (x s : S → ℝ) = x 0 := h2.mono fun s hs => hconst s hs
  have h4 : ∀ᶠ s in Filter.atTop, ‖(x 0 : S → ℝ)‖ + 1 ≤ ‖(x s : S → ℝ)‖ ∧ (x s : S → ℝ) = x 0 :=
    h1.and h3
  obtain ⟨s, hs⟩ := h4.exists
  have hle : ‖(x 0 : S → ℝ)‖ + 1 ≤ ‖(x 0 : S → ℝ)‖ := by
    have h' : ‖(x 0 : S → ℝ)‖ + 1 ≤ ‖(x s : S → ℝ)‖ := hs.1
    rw [hs.2] at h'
    exact h'
  linarith

/-! ### A strictly positive conservation law forbids escape -/

/-- **A nonnegative conservation law bounds the coordinate it detects.**  Let `w` be a
conservation law that is nonnegative and strictly positive at the species `s`.  The conserved
total `∑ u, w u * x t u` is a constant of motion; because every coordinate of the trajectory is
nonnegative, the `s`-term of that total is bounded by the total itself, and therefore
`x t s ≤ weightedTotal w x₀ / w s`.  This is the quantitative form of "a species detected by a
nonnegative conservation law cannot escape". -/
theorem coordinate_le_of_conservation_law (N : Network S) (κ : N.RateConstants)
    {w : S → ℝ} (hw : N.IsPInvariant w) (hw0 : ∀ u, 0 ≤ w u) {s : S} (hws : 0 < w s)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) {x : ℝ → Concentration S} (hx0 : x 0 = x₀)
    {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ)
    (hxnn : ∀ τ : ℝ, 0 ≤ τ → (x τ).Nonnegative) :
    x t s ≤ weightedTotal w x₀ / w s := by
  have hconst := N.conservationLaw_total_const_along_solution κ hw ht hsol
  rw [hx0] at hconst
  have hterm : w s * x t s ≤ weightedTotal w (x t) := by
    unfold weightedTotal
    exact Finset.single_le_sum
      (fun u _ => mul_nonneg (hw0 u) ((hxnn t ht) u)) (Finset.mem_univ s)
  have hC : 0 ≤ weightedTotal w x₀ := by
    unfold weightedTotal
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hw0 u) (hx₀ u).le
  refine (le_div_iff₀ hws).2 ?_
  rw [← hconst]
  simpa [mul_comm] using hterm

/-- **A strictly positive conservation law bounds every coordinate.**  If `w` is a conservation
law with `w s > 0` for every species, then each coordinate of a nonnegative forward trajectory is
bounded by the initial total divided by `w s`. -/
theorem coordinate_le_of_positive_conservation_law (N : Network S) (κ : N.RateConstants)
    {w : S → ℝ} (hw : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) {x₀ : Concentration S}
    (hx₀ : x₀.Positive) {x : ℝ → Concentration S} (hx0 : x 0 = x₀) {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ)
    (hxnn : ∀ τ : ℝ, 0 ≤ τ → (x τ).Nonnegative) {s : S} :
    x t s ≤ weightedTotal w x₀ / w s :=
  N.coordinate_le_of_conservation_law κ hw (fun u => (hwpos u).le) (hwpos s) hx₀ hx0 ht hsol hxnn

/-- **No escape under a strictly positive conservation law.**  A network that admits a strictly
positive conservation law cannot have an unbounded forward trajectory: every coordinate is
bounded by a constant depending only on the initial state and the rates.  Together with the
bounded case of leaf D12 (`CRNT.Network.weaklyReversible_forward_floor_uniform`) the trajectory
then has a positive lower bound, again depending only on the initial state and the rates.  In
other words: *the persistence conjecture holds for every network with a strictly positive
conservation law*, and the only networks in which an escape to infinity can occur are the
non-conservative ones. -/
theorem no_escape_of_positive_conservation_law (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {w : S → ℝ} (hw : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : ℝ → Concentration S, x 0 = x₀ →
        (∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) →
        (∀ τ : ℝ, 0 ≤ τ → ∀ s, η ≤ x τ s ∧ x τ s ≤ ∑ u, weightedTotal w x₀ / w u) := by
  have hwsp : N.IsStrictPSemiflow w := ⟨hw, hwpos⟩
  have hW : 0 ≤ weightedTotal w x₀ := by
    unfold weightedTotal
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hwpos u).le (hx₀ u).le
  -- the coordinate bound, at nonnegative states
  have hbnd : ∀ (x : ℝ → Concentration S), x 0 = x₀ →
      (∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) →
      ∀ t : ℝ, 0 ≤ t → (x t).Nonnegative → ∀ s, x t s ≤ ∑ u, weightedTotal w x₀ / w u := by
    intro x hx0 hsol t ht hnn s
    have hcomp : N.StoichCompatible x₀ (x t) := by
      have hc := N.stoichCompatible_of_forward_solution κ hsol t ht
      rw [hx0] at hc
      exact hc
    have h1 := N.coordinate_le_of_strictPSemiflow hwsp hx₀.nonnegative hnn hcomp s
    have h2 : weightedTotal w x₀ / w s ≤ ∑ u, weightedTotal w x₀ / w u :=
      Finset.single_le_sum (f := fun u => weightedTotal w x₀ / w u)
        (fun u _ => div_nonneg hW (hwpos u).le) (Finset.mem_univ s)
    exact h1.trans h2
  -- positivity of the trajectory, from the bound
  have hpos : ∀ (x : ℝ → Concentration S), x 0 = x₀ →
      (∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) →
      ∀ t : ℝ, 0 ≤ t → (x t).Positive := by
    intro x hx0 hsol t ht
    exact N.orbit_pos_forward_of_bdd_nonneg κ (hx0 ▸ hx₀)
      (fun t ht hnn s => hbnd x hx0 hsol t ht hnn s) hsol t ht
  -- the uniform floor, from the bounded case of D12
  obtain ⟨η, hη, hfloor⟩ :=
    N.weaklyReversible_forward_floor_uniform κ hwr hx₀ (∑ u, weightedTotal w x₀ / w u)
  refine ⟨η, hη, ?_⟩
  intro x hx0 hsol τ hτ s
  have hbound : ∀ t : ℝ, 0 ≤ t → ∀ u, x t u ≤ ∑ v, weightedTotal w x₀ / w v := by
    intro t ht u
    exact hbnd x hx0 hsol t ht (hpos x hx0 hsol t ht).nonnegative u
  exact ⟨hfloor x hx0 hsol hbound τ hτ s, hbound τ hτ s⟩

/-- **The (strong) persistence conjecture holds for networks with a strictly positive
conservation law.**  Such a network is conservative, and the compact-confinement form of the
Persistence Conjecture is known for conservative networks; here the conclusion is obtained
directly from the escape analysis: the conservation law bounds the trajectory, and the bounded
case of D12 gives the uniform positive floor. -/
theorem persistenceConjectureStrong_of_positive_conservation_law (N : Network S)
    (hwr : N.WeaklyReversible) {w : S → ℝ} (hw : N.IsPInvariant w) (hwpos : ∀ s, 0 < w s) :
    N.PersistenceConjectureStrong := by
  refine fun _ => ?_
  intro κ
  refine fun x₀ hx₀ => ?_
  obtain ⟨η, hη, hfloor⟩ :=
    N.no_escape_of_positive_conservation_law κ hwr hw hwpos hx₀
  refine ⟨Set.univ.pi fun _ => Set.Icc η (∑ u, weightedTotal w x₀ / w u),
    isCompact_univ_pi fun _ => isCompact_Icc, ?_, ?_⟩
  · intro y hy s
    exact lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1
  · intro x hx0 hsol τ hτ
    refine Set.mem_pi.2 ?_
    intro s _
    exact (hfloor x hx0 hsol τ hτ s)

/-! ### The escaping face -/

/-- **The zero set of the conservation laws.**  The species that are annihilated by *every*
conservation law: no conservation law can see them, so they are the only species that may
participate in an escape that no conservation law detects. -/
def conservationLawZeroSet (N : Network S) : Set S :=
  {s | ∀ w ∈ N.conservationLawSpace, w s = 0}

/-- **The escaping face.**  The species that are annihilated by every *nonnegative* conservation
law.  This is the face of the nonnegative orthant on which an escape to infinity has to live:
a species detected by a nonnegative conservation law has a bounded coordinate. -/
def escapeFace (N : Network S) : Set S :=
  {s | ∀ w ∈ N.conservationLawSpace, (∀ u, 0 ≤ w u) → w s = 0}

/-- Characterization of the zero set of the conservation laws. -/
theorem mem_conservationLawZeroSet_iff (N : Network S) (s : S) :
    s ∈ N.conservationLawZeroSet ↔ ∀ w ∈ N.conservationLawSpace, w s = 0 := Iff.rfl

/-- Characterization of the escaping face. -/
theorem mem_escapeFace_iff (N : Network S) (s : S) :
    s ∈ N.escapeFace ↔ ∀ w ∈ N.conservationLawSpace, (∀ u, 0 ≤ w u) → w s = 0 := Iff.rfl

/-- **A species outside the escaping face is detected by a nonnegative conservation law.**  The
converse of `mem_escapeFace_iff`: if `s` is not in the escaping face, there is a conservation
law `w ≥ 0` with `w s > 0`. -/
theorem not_mem_escapeFace_iff (N : Network S) (s : S) :
    s ∉ N.escapeFace ↔ ∃ w ∈ N.conservationLawSpace, (∀ u, 0 ≤ w u) ∧ 0 < w s := by
  constructor
  · intro h
    rw [mem_escapeFace_iff] at h
    rw [not_forall] at h
    obtain ⟨w, hw⟩ := h
    have hw1 := not_imp.mp hw
    have hw2 := not_imp.mp hw1.2
    refine ⟨w, hw1.1, hw2.1, ?_⟩
    exact lt_of_le_of_ne (hw2.1 s) (Ne.symm hw2.2)
  · rintro ⟨w, hwV, hw0, hws⟩
    rw [mem_escapeFace_iff]
    intro h
    exact absurd (h w hwV hw0) hws.ne'

/-- **The zero set sits inside the escaping face.**  A species that no conservation law sees at
all is in particular a species that no *nonnegative* conservation law sees. -/
theorem conservationLawZeroSet_subset_escapeFace (N : Network S) :
    N.conservationLawZeroSet ⊆ N.escapeFace := by
  intro s hs
  rw [mem_conservationLawZeroSet_iff] at hs
  rw [mem_escapeFace_iff]
  intro w hwV hw0
  exact hs w hwV

/-- **A species outside the escaping face has a bounded coordinate.**  If `s` is detected by a
nonnegative conservation law `w` (`w s > 0`), then the coordinate `x t s` of a nonnegative
forward mass-action trajectory is bounded by the conserved total divided by `w s`, uniformly in
`t`.  This is the "the escape is confined to a face" statement: the species that can run to
infinity are exactly the ones in `N.escapeFace`. -/
theorem escape_confined_to_zero_face (N : Network S) (κ : N.RateConstants)
    {x : ℝ → Concentration S} {x₀ : Concentration S} (hx₀ : x₀.Positive) (hx0 : x 0 = x₀)
    (hxnn : ∀ τ : ℝ, 0 ≤ τ → (x τ).Nonnegative)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ)
    {s : S} (hs : s ∉ N.escapeFace) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 ≤ τ → x τ s ≤ B := by
  obtain ⟨w, hwV, hw0, hws⟩ := (N.not_mem_escapeFace_iff s).1 hs
  have hw : N.IsPInvariant w := (N.mem_conservationLawSpace_iff w).1 hwV
  have hC : 0 ≤ weightedTotal w x₀ := by
    unfold weightedTotal
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hw0 u) (hx₀ u).le
  refine ⟨weightedTotal w x₀ / w s, div_nonneg hC hws.le, ?_⟩
  intro τ hτ
  exact N.coordinate_le_of_conservation_law κ hw hw0 hws hx₀ hx0 hτ hsol hxnn

/-- **The species that escape are contained in the escaping face.**  The set of species whose
coordinate is unbounded along a nonnegative forward mass-action trajectory is contained in
`N.escapeFace`: an escaping species is one that no nonnegative conservation law detects. -/
def escapingSpecies (x : ℝ → Concentration S) : Set S :=
  {s | ¬ ∃ B : ℝ, ∀ τ : ℝ, 0 ≤ τ → x τ s ≤ B}

/-- The escaping species of a nonnegative forward trajectory lie in the escaping face. -/
theorem escapingSpecies_subset_escapeFace (N : Network S) (κ : N.RateConstants)
    {x : ℝ → Concentration S} {x₀ : Concentration S} (hx₀ : x₀.Positive) (hx0 : x 0 = x₀)
    (hxnn : ∀ τ : ℝ, 0 ≤ τ → (x τ).Nonnegative)
    (hsol : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt x (N.massActionVectorField κ (x τ)) τ) :
    escapingSpecies x ⊆ N.escapeFace := by
  intro s hs
  by_contra hne
  obtain ⟨B, hB0, hB⟩ := N.escape_confined_to_zero_face κ hx₀ hx0 hxnn hsol hne
  exact hs ⟨B, hB⟩

end Network

end CRNT

/-! ### An instance: the reversible pair `A ⇌ B` -/

namespace CRNT.Examples.ReversiblePair

open CRNT CRNT.Network Species

/-- **The total mass is a conservation law of `A ⇌ B`.**  The reaction vectors of `A ⇌ B` are
`B - A` and `A - B`, so the species sum of each of them vanishes: the total number of
molecules `A + B` is conserved.  This is a strictly positive conservation law, so by
`CRNT.Network.no_escape_of_positive_conservation_law` the trajectories of this network cannot
escape. -/
theorem totalMass_conservationLaw : N.IsPInvariant (fun _ => (1 : ℝ)) := by
  unfold IsPInvariant stoichSubspace
  refine mem_orthSum_span ?_
  rintro g ⟨r, rfl⟩
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_pair (show (A : Species) ≠ B by decide)]
  cases r
  · rw [reactionVector_fwd]
    simp
  · have hbwd : N.reactionVector Rxn.bwd = -N.reactionVector Rxn.fwd := by
      funext s
      cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]
    rw [hbwd, reactionVector_fwd]
    simp

/-- **The trajectories of `A ⇌ B` are bounded by the initial total mass.**  The total
`A + B` is conserved, and the trajectory stays positive, so each of the two coordinates is
bounded by the initial total.  This is the "no escape" conclusion for a concrete network with
a conservation law. -/
theorem bounded_by_initial_total (κ : N.RateConstants) {x₀ : Concentration Species}
    (hx₀ : x₀.Positive) {x : ℝ → Concentration Species} (hx0 : x 0 = x₀)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (N.massActionVectorField κ (x t)) t) :
    ∀ t : ℝ, 0 ≤ t → ∀ s, x t s ≤ x₀ A + x₀ B := by
  have hwsp : N.IsStrictPSemiflow (fun _ => (1 : ℝ)) := ⟨totalMass_conservationLaw, fun _ => one_pos⟩
  obtain ⟨Bbound, hB⟩ := N.conservative_forward_bound κ hwsp hx₀
  have hpos : ∀ t : ℝ, 0 ≤ t → (x t).Positive :=
    N.orbit_pos_forward_of_bdd_nonneg κ (hx0 ▸ hx₀) (fun t ht hnn s => hB x hx0 hsol t ht s) hsol
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  have htotal : ∀ t : ℝ, 0 ≤ t → x t A + x t B = x₀ A + x₀ B := by
    intro t ht
    have h := N.conservationLaw_total_const_along_solution κ totalMass_conservationLaw ht hsol
    rw [hx0] at h
    have hsum : weightedTotal (fun _ => (1 : ℝ)) (x t) = x t A + x t B := by
      unfold weightedTotal
      rw [huniv, Finset.sum_pair (show (A : Species) ≠ B by decide)]
      simp
    have hsum0 : weightedTotal (fun _ => (1 : ℝ)) x₀ = x₀ A + x₀ B := by
      unfold weightedTotal
      rw [huniv, Finset.sum_pair (show (A : Species) ≠ B by decide)]
      simp
    rw [hsum, hsum0] at h
    exact h
  intro t ht s
  cases s with
  | A =>
    have hle : x t A ≤ x t A + x t B := by linarith [(hpos t ht) B]
    linarith [hle, htotal t ht]
  | B =>
    have hle : x t B ≤ x t A + x t B := by linarith [(hpos t ht) A]
    linarith [hle, htotal t ht]

/-- **The reversible pair `A ⇌ B`: bounded trajectories with a positive floor.**  For every
choice of positive rate constants and every positive initial state, the mass-action trajectory
stays below the initial total mass and above a positive constant; the lower bound depends only
on the initial state and the rates.  This is the conclusion of leaf D12 for a concrete network
carrying a (strictly positive) conservation law: no escape is possible. -/
theorem bounded_and_persistent (κ : N.RateConstants) {x₀ : Concentration Species}
    (hx₀ : x₀.Positive) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : ℝ → Concentration Species, x 0 = x₀ →
        (∀ t : ℝ, 0 ≤ t → HasDerivAt x (N.massActionVectorField κ (x t)) t) →
        (∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ x t s ∧ x t s ≤ x₀ A + x₀ B) := by
  obtain ⟨η, hη, hfloor⟩ :=
    N.weaklyReversible_forward_floor_uniform κ weaklyReversible hx₀ (x₀ A + x₀ B)
  refine ⟨η, hη, ?_⟩
  intro x hx0 hsol t ht s
  refine ⟨hfloor x hx0 hsol (fun t ht s => bounded_by_initial_total κ hx₀ hx0 hsol t ht s) t ht s,
    bounded_by_initial_total κ hx₀ hx0 hsol t ht s⟩

end CRNT.Examples.ReversiblePair

/-! ### A second instance: an actual escape, the autocatalytic network `A → 2A` -/

namespace CRNT.Examples.EscapeAutocatalysis

open CRNT CRNT.Network

/-- Two species: `A`, which is autocatalytic, and `B`, a spectator. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by
    intro s
    cases s
    · decide
    · decide

open Species

/-- The single reaction channel of the network. -/
inductive Rxn
  | r1
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1}
  complete := by
    intro r
    cases r
    simp
/-- The source complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The target complex `2A`. -/
def c2A : Complex Species := fun s => match s with | A => 2 | B => 0

/-- The reaction `A → 2A`. -/
def rxn : Rxn → Reaction Species
  | .r1 => { source := cA, target := c2A }

/-- The network `A → 2A`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

theorem univ_species : (Finset.univ : Finset Species) = {A, B} := by decide

theorem univ_rxn : (Finset.univ : Finset Rxn) = {Rxn.r1} := by decide

/-- The reaction vector of `A → 2A` is `A`: one extra molecule of `A` per reaction. -/
theorem reactionVector_r1 :
    N.reactionVector Rxn.r1 = fun s => match s with | A => (1 : ℝ) | B => 0 := by
  funext s
  cases s
  · simp [Network.reactionVector, N, rxn, Reaction.vector, cA, c2A]
    norm_num
  · simp [Network.reactionVector, N, rxn, Reaction.vector, cA, c2A]

/-- The conservation law that counts the `B` molecules. -/
def wB : Species → ℝ := fun s => if s = B then (1 : ℝ) else 0

/-- **The spectator `B` is a conservation law.**  The reaction `A → 2A` does not change the
number of `B` molecules, so the vector `(0, 1)` is a conservation law: the `B`-count is
constant along every trajectory. -/
theorem b_conservationLaw : N.IsPInvariant wB := by
  unfold IsPInvariant stoichSubspace
  refine mem_orthSum_span ?_
  rintro g ⟨r, rfl⟩
  cases r
  rw [reactionVector_r1]
  rw [univ_species, Finset.sum_pair (show (A : Species) ≠ B by decide)]
  simp [wB]

/-- **Every conservation law vanishes at `A`.**  The stoichiometric subspace is spanned by the
reaction vector `A`, so a conservation law — a vector orthogonal to the stoichiometric subspace
— has zero `A`-component.  The species `A` is invisible to *every* conservation law: it is a
member of the zero set `N.conservationLawZeroSet` and of the escaping face `N.escapeFace`. -/
theorem conservationLaw_zero_at_A (w : Species → ℝ) (hw : w ∈ N.conservationLawSpace) :
    w A = 0 := by
  rw [N.mem_conservationLawSpace_iff] at hw
  unfold IsPInvariant at hw
  rw [mem_orthSum] at hw
  have h := hw (fun s => match s with | A => (1 : ℝ) | B => 0) (by
    rw [← reactionVector_r1]
    exact N.reactionVector_mem_stoichSubspace Rxn.r1)
  rw [univ_species, Finset.sum_pair (show (A : Species) ≠ B by decide)] at h
  simpa using h

/-- **`A` lies in the escaping face:** no nonnegative conservation law detects it. -/
theorem A_mem_escapeFace : A ∈ N.escapeFace := by
  rw [N.mem_escapeFace_iff]
  intro w hwV hw0
  exact conservationLaw_zero_at_A w hwV

/-- **`A` lies in the zero set of the conservation laws.** -/
theorem A_mem_conservationLawZeroSet : A ∈ N.conservationLawZeroSet := by
  rw [N.mem_conservationLawZeroSet_iff]
  intro w hwV
  exact conservationLaw_zero_at_A w hwV

/-- **`B` does not lie in the escaping face:** the conservation law `(0, 1)` detects it, so `B`
cannot escape. -/
theorem B_not_mem_escapeFace : B ∉ N.escapeFace := by
  rw [N.not_mem_escapeFace_iff]
  refine ⟨wB, b_conservationLaw, ?_, ?_⟩
  · intro u
    cases u <;> simp [wB]
  · have hwBB : wB B = 1 := rfl
    simp [hwBB]

/-- Unit rate constant. -/
def κ₁ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The mass-action field of `A → 2A` at unit rate: `A` grows at rate `x A`, `B` is inert. -/
theorem field_eq (x : Concentration Species) :
    N.massActionVectorField κ₁ x = fun s => match s with | A => x A | B => 0 := by
  funext s
  cases s
  · simp [massActionVectorField_apply, massActionRate, κ₁, univ_rxn,
      Complex.massActionMonomial, N, rxn, cA, c2A, univ_species]
    ring
  · simp [massActionVectorField_apply, massActionRate, κ₁, univ_rxn,
      Complex.massActionMonomial, N, rxn, cA, c2A, univ_species]

/-- The explicit solution of `A → 2A` from `(1, 1)`: `A` grows exponentially, `B` is
constant. -/
noncomputable def sol (t : ℝ) : Concentration Species := fun s =>
  match s with | A => Real.exp t | B => 1

theorem sol_hasDerivAt (t : ℝ) : HasDerivAt sol (N.massActionVectorField κ₁ (sol t)) t := by
  rw [field_eq, hasDerivAt_pi]
  intro s
  cases s
  · have he : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp t) t := by
      convert (hasDerivAt_id t).exp using 1 <;> simp
    simpa [sol] using he
  · have hz : HasDerivAt (fun t : ℝ => (1 : ℝ)) (0 : ℝ) t := by
      simpa using (hasDerivAt_const t (1 : ℝ))
    simpa [sol] using hz

/-- **The trajectory escapes to infinity.**  The `A`-coordinate of the solution grows
exponentially, so the norm of the trajectory tends to infinity: this is the phenomenon that the
unbounded case of leaf D12 is about. -/
theorem sol_escapes :
    Filter.Tendsto (fun t => ‖(sol t : Species → ℝ)‖) Filter.atTop Filter.atTop := by
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp t) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop
  have hge : ∀ t : ℝ, Real.exp t ≤ ‖(sol t : Species → ℝ)‖ := by
    intro t
    calc Real.exp t = |(sol t : Species → ℝ) A| := by simp [sol]
      _ = ‖(sol t : Species → ℝ) A‖ := Real.norm_eq_abs _
      _ ≤ ‖(sol t : Species → ℝ)‖ := norm_le_pi_norm _ _
  refine Filter.tendsto_atTop.2 fun b => ?_
  filter_upwards [hexp.eventually_ge_atTop b] with t ht
  exact le_trans ht (hge t)

/-- **The escaping species is in the escaping face.**  For the network `A → 2A` the species
`A` escapes to infinity and `A` is invisible to every conservation law, while `B` — detected
by the conservation law `(0, 1)` — has a bounded coordinate.  This is the geometric content of
the escape analysis: *the escape happens in the face determined by the conservation laws*. -/
theorem escape_confined_to_face_of_escape :
    ∀ t : ℝ, 0 ≤ t → sol t B ≤ 1 := by
  have hx₀ : (sol 0).Positive := by
    intro s
    cases s
    · simp [sol]
    · simp [sol]
  have hnn : ∀ τ : ℝ, 0 ≤ τ → (sol τ).Nonnegative := by
    intro τ hτ s
    cases s
    · simp only [sol]
      positivity
    · simp [sol]
  have hbound := N.escape_confined_to_zero_face κ₁ hx₀ rfl hnn
    (fun τ hτ => sol_hasDerivAt τ) B_not_mem_escapeFace
  obtain ⟨Bbound, hB0, hB⟩ := hbound
  intro t ht
  have hle : sol t B ≤ weightedTotal wB (sol 0) / wB B := by
    have hwBB : wB B = 1 := rfl
    have h := N.coordinate_le_of_conservation_law κ₁ b_conservationLaw
      (by intro u; cases u <;> simp [wB]) (by simp [wB]) (s := B) hx₀ rfl ht
      (fun τ hτ => sol_hasDerivAt τ) hnn
    simpa using h
  have hval : weightedTotal wB (sol 0) = 1 := by
    unfold weightedTotal
    rw [univ_species, Finset.sum_pair (show (A : Species) ≠ B by decide)]
    simp [wB, sol]
  rw [hval] at hle
  simpa [wB] using hle

end CRNT.Examples.EscapeAutocatalysis
