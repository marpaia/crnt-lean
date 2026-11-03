import CRNT.Dynamics.HighCodimensionSiphonFace

/-!
# Adjudication: `exists_positive_omegaPoint_of_upperRegion` cannot be applied under the
# hypotheses of the Global Attractor hole

`CRNT/Dynamics/HighCodimensionSiphonFace.lean:135` carries the tree's single remaining
obligation for `Network.complexBalanced_genuinePermanent`.  Two candidate endgames were
under consideration for it, and they were believed to be mutually exclusive:

* `exists_positive_omegaPoint_of_upperRegion` (same file, :1596), whose only unbuilt inputs
  are `hfloor` and the non-crossing condition `hsplit`;
* the packaged barrier/blueprint criteria reachable through `CRNT.Geometry.CraciunZSH`.

They **are** mutually exclusive, and this module settles which side of the fork the hole
falls on, by machine check rather than by argument.

## The verdict

`false_of_upperRegion_and_boundaryOmegaPoint` below: take *every* hypothesis of
`exists_positive_omegaPoint_of_upperRegion` — including `hfloor` — together with the
ω-limit-set hypotheses the hole supplies (`hwmax`, `hPmaxne`, `hzeroMax`), and conclude
`False`.

So `hfloor` is not an "unbuilt input" that a later researcher is expected to discharge. It
is a hypothesis that is **unsatisfiable** under the hole's own hypotheses, and establishing
it proves the full Global Attractor Conjecture in a degenerate way (every ω-point would be
strictly positive, so no ω-point could vanish anywhere at all).

## Why, and where the disagreement came from

The intuition that `hfloor` is "a floor on a *region*, not along the orbit" and is therefore
untouched by the orbit-level obstructions is correct as far as it goes, and it is exactly the
intuition that makes `exists_positive_omegaPoint_of_upperRegion` look like the live route.
The obstruction is one step further along, and it is a step the criterion's own proof takes:

1. `orbit_stays_in_upperRegion` (`HighCodimensionSiphonFace.lean:1508`) turns non-crossing
   (`hsplit`) plus the start point `hx₀Z` into `γ x₀ t ∈ Zupper` for **all** forward `t`.  So
   the whole forward orbit lies in `Zupper`, hence in `closure Zupper`.
2. Every ω-limit point lies in the closure of the forward orbit's image
   (`omegaLimit_subset_closure_image2`).  Hence `ω ⊆ closure Zupper`.
3. `hfloor` is stated on `Zupper`, but the criterion consumes it through
   `closure_minimal … hFloorClosed`, i.e. as `closure Zupper ⊆ {y | ∀ s, ε ≤ y s}` — a
   statement about the **closure**, not about `Zupper`.  The floor therefore does reach `ω`.
4. So every ω-point is strictly positive.  Under `hzeroMax` and `hPmaxne` the hole's `wmax`
   has a zero coordinate and is in `ω`.  Contradiction.

The criterion's own proof carries this through `hKpos : ∀ y ∈ K, Positive y` with
`K = closure Zupper ∩ {…}`, which is the same step packaged.  We reproduce only the part
needed for the contradiction; neither the entropy level nor compactness is needed, because
steps 1–3 already give `∀ s, ε ≤ wmax s`.

## The general mechanism

`positive_omegaLimit_of_confinedToFlooredRegion` isolates the whole mechanism with **no**
reaction-network structure: mass-action field, complex balancedness, relative-entropy level,
compactness and orbit-compactness all absent.  The conclusion is forced by topology alone.
That is why it cannot be evaded by refining the CRNT-specific parts of the criterion — and it
is the same shape as the `Permanent`-based obstruction: a compact positive confining set
absorbs the orbit closure, ω lies in it, and hence *every* ω-point is positive.

## Consequence for route selection

`exists_positive_omegaPoint_of_upperRegion` is **not** the endgame for this hole.  It is a
correct theorem about a situation that cannot arise here.  Every packaged criterion whose
`hsep` is a coordinate floor is refuted by the same mechanism.

This is a statement about the *routes*, not about the hole's truth: the hole's own hypotheses
remain consistent and are not assumed here.  What this does **not** decide is whether the hole
is provable by some other route.  For that, see `docs/hole-reachability.md`, whose
"Available-but-unused capabilities" section lists — computed, not curated — the proved,
hole-free modules that already sit in each hole's import closure and are never used.

Depends on: `CRNT.Dynamics.HighCodimensionSiphonFace` (for `orbit_stays_in_upperRegion`),
`CRNT.Dynamics.EndotacticPermanence` (for `omegaLimit_subset_closure_image2`).
-/

open scoped NNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Adjudication: the upper-region criterion's `hfloor` is unsatisfiable whenever the
ω-limit set has a non-positive point.**

Take exactly the hypotheses of `exists_positive_omegaPoint_of_upperRegion`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:1596`) — in particular `hfloor`, the floor on
the upper region — together with three ω-limit hypotheses: `wmax ∈ ω`, `Pmax` nonempty, and
`∀ s, s ∈ Pmax ↔ wmax s = 0`.  Those are `hwmax`, `hPmaxne`, `hzeroMax` at the hole
`CRNT/Dynamics/HighCodimensionSiphonFace.lean:135`.

The proof runs the criterion's own steps and stops as soon as they conflict:

* `hstay`: the whole forward orbit stays in `Zupper`, by `orbit_stays_in_upperRegion` driven by
  non-crossing `hsplit` and the start point `hx₀Z`;
* `hω`: every ω-limit point is in `closure Zupper`, since ω-limit points lie in the closure of
  the orbit image and the orbit image lies in `Zupper`;
* `hfloorC`: `hfloor` survives passage to the closure, so `∀ s, ε ≤ wmax s`, and `hε : 0 < ε`
  makes `wmax` strictly positive;
* contradiction with `hzeroMax` at any member of the nonempty `Pmax`.

Consequently no construction of `Zlow`, `Zupper`, `ε`, `hsplit` and `hfloor` can be supplied
from the hole's hypotheses: that system of hypotheses is already contradictory. -/
theorem false_of_upperRegion_and_boundaryOmegaPoint
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hx₀ : x₀.Positive)
    {Zlow Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hopenLow : IsOpen Zlow) (hopenUp : IsOpen Zupper) (hdisj : Disjoint Zlow Zupper)
    (hsplit : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ Zlow ∪ Zupper)
    (hx₀Z : x₀ ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ (s : S), ε ≤ y s)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    (hzeroMax : ∀ (s : S), s ∈ Pmax ↔ wmax s = 0) :
    False := by
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  -- Step 1: non-crossing keeps the whole forward orbit in `Zupper`.
  have hstay : ∀ t, 0 ≤ t → γ x₀ t ∈ Zupper :=
    orbit_stays_in_upperRegion
      (fun t ht => ((hsol t ht).continuousAt).continuousWithinAt)
      hopenLow hopenUp hdisj hsplit (by rw [hγ0]; exact hx₀Z)
  -- Step 2: the forward orbit image lies in `closure Zupper`, and so does `ω`.
  have himgZ : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ closure Zupper := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hϕγ x t]
    exact subset_closure (hstay (t : ℝ) t.coe_nonneg)
  have hωZ : omegaLimit atTop ϕ {x₀} ⊆ closure Zupper := by
    intro y hy
    have h1 := (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem) hy
    exact (closure_minimal (fun z hz => himgZ hz) isClosed_closure) h1
  -- Step 3: `hfloor` is consumed through `closure Zupper`, so it reaches `wmax`.
  have hFloorClosed : IsClosed {y : Concentration S | ∀ (s : S), ε ≤ y s} := by
    have hrw : {y : Concentration S | ∀ (s : S), ε ≤ y s} = ⋂ s : S, {y | ε ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hfloorC : closure Zupper ⊆ {y | ∀ (s : S), ε ≤ y s} :=
    closure_minimal (fun y hy s => hfloor y hy s) hFloorClosed
  have hwmaxFloor : ∀ (s : S), ε ≤ wmax s := hfloorC (hωZ hwmax)
  -- Step 4: `wmax` is strictly positive, which its zero coordinates forbid.
  obtain ⟨s₀, hs₀⟩ := hPmaxne
  have hz : wmax s₀ = 0 := (hzeroMax s₀).mp hs₀
  have hp : 0 < wmax s₀ := lt_of_lt_of_le hε (hwmaxFloor s₀)
  exact hp.ne' hz

omit [DecidableEq S] [Fintype S] in
/-- **The general mechanism, with no reaction-network structure at all.**

If the forward orbit of `x₀` under `ϕ` stays inside a set `Zupper` carrying a uniform positive
floor `ε` on every coordinate, then *every* ω-limit point is strictly positive.

No mass-action field, no complex balancedness, no relative-entropy level, no compactness and
no orbit-compactness hypothesis appears.  That is the point: the conclusion is forced by
topology alone, which is why it cannot be evaded by refining any of the CRNT-specific parts
of `exists_positive_omegaPoint_of_upperRegion`.  The mechanism is the same one that makes
`Permanent` (`CRNT/Dynamics/EndotacticPermanence.lean:58`) so strong: a positive confining set
absorbs the orbit closure, ω lies in it, so every ω-point is positive. -/
theorem positive_omegaLimit_of_confinedToFlooredRegion
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {Zupper : Set (Concentration S)} {ε : ℝ} (hε : 0 < ε)
    (hconf : ∀ t : ℝ, 0 ≤ t → γ x₀ t ∈ Zupper)
    (hfloor : ∀ y ∈ Zupper, ∀ (s : S), ε ≤ y s) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, y.Positive := by
  have hFloorClosed : IsClosed {y : Concentration S | ∀ (s : S), ε ≤ y s} := by
    have hrw : {y : Concentration S | ∀ (s : S), ε ≤ y s} = ⋂ s : S, {y | ε ≤ y s} := by
      ext y; simp [Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have hfloorC : closure Zupper ⊆ {y | ∀ (s : S), ε ≤ y s} :=
    closure_minimal (fun y hy s => hfloor y hy s) hFloorClosed
  have himgZ : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ closure Zupper := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hϕγ x t]
    exact subset_closure (hconf (t : ℝ) t.coe_nonneg)
  have hωZ : omegaLimit atTop ϕ {x₀} ⊆ closure Zupper := by
    intro y hy
    have h1 := (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
      (u := Set.univ) univ_mem) hy
    exact (closure_minimal (fun z hz => himgZ hz) isClosed_closure) h1
  intro y hy s
  exact lt_of_lt_of_le hε (hfloorC (hωZ hy) s)

omit [DecidableEq S] [Fintype S] in
/-- **The universal-positive form: the single template that retires the whole family.**

If the forward orbit of `x₀` under `ϕ` is eventually contained in a set `K` that is *closed*
and *pointwise strictly positive*, then **every** ω-limit point is strictly positive.

This is strictly more general than `positive_omegaLimit_of_confinedToFlooredRegion`: a uniform
floor on a set whose closure traps the orbit is one way to produce such a `K`, but any
closed, pointwise-positive confining set does, however it was obtained — and the hypothesis
here is a bare set-theoretic condition, with no floor, no `ε`, no concentration structure and
no reaction network at all.

**Why this is the right thing to state.** The hole
`exists_positive_omegaPoint_of_highCodimension_siphonFace` asks for
`∃ p ∈ omegaLimit, p.Positive` **while permitting** a boundary ω-point (`hwmax`,
`hzeroMax`, `hPmaxne`). This lemma yields the *universal* form `∀ w ∈ omegaLimit, w.Positive`,
which is exactly the negation of that permission. So **every** criterion in the tree whose
orbit-confinement is discharged by a closed pointwise-positive set is unusable here for one
structural reason, not for a reason particular to any of them — among them
`PersistentOrbit.omegaLimit_positive` (`GlobalPersistence.lean:161`),
`exists_positive_omegaPoint_of_upperRegion`,
`not_persistentFrom_of_mem_omegaLimit_notPositive`
(`HighCodimensionSiphonFace.lean:407`) and `NoCriticalSiphonPersistence`.

**Provenance — this is not a new obstruction, it is an existing one shown to be uniform.**
`PersistentOrbit.omegaLimit_positive` (`CRNT/Dynamics/GlobalPersistence.lean:161`) already
proved the ∀-form before this module existed, by the same argument: a per-coordinate floor
along the orbit, transported to the closure of the orbit image, reaching `ω`. What is new
here is that the *floor is not needed* — an arbitrary closed, everywhere-positive set
suffices. `PersistentOrbit`'s confine is an intersection of coordinate half-spaces, which is
precisely the `hfloor`/`hsep` shape the hole cannot supply, so this generalization widens the
template without changing which callers are affected. Related instances already in the tree:
`NoCriticalSiphonPersistence.lean:45` and `NoDrainableSiphonPersistence.lean:40`.

**Scope, stated precisely so the entry cannot be over-read.** This lemma is *not* an
impossibility result: closed, everywhere-positive confining sets exist and plenty of
theorems build them (`isCompact_relEntropy_sublevel`, `persistentFrom_of_upperRegion`, and
the GAC chain itself at `GACNoCriticalSiphon.lean:158`, which *derives* `hωpos :
∀ y ∈ omegaLimit, y.Positive` and feeds it onward). What the lemma says is that such a set
**discharges**: it converts the existential conclusion into the universal one. The
contradiction is not intrinsic to the template; it arises when the caller *also* supplies a
boundary ω-point, as Hole A does via `hwmax`, `hzeroMax` and `hPmaxne`. Read it as "no
criterion *for this hole* may discharge through a closed positive confine", not as "closed
positive confines are impossible".

**What the template does *not* reach.** It does not by itself retire the `hsep`-family of
the packaged barrier criteria: `hsep` bounds coordinates away from the coordinate
hyperplanes, which is a different shape of hypothesis from "the orbit is confined to a
closed positive set". Those are refuted by the barrier-free lemma that a uniform coordinate
floor along the forward orbit forces the same floor on every ω-limit point — a separate
argument on a separate shape. The two obstructions are independent, and the `hsep` one does
not go away just because this template is available.

The practical rule this yields: *a criterion for this hole must not confine the orbit to a
closed, everywhere-positive set.* Whatever the geometry, that converts an existential
conclusion into a universal one and negates the hole's hypothesis. -/
theorem universalPositive_omegaLimit_of_closedPositiveConfine
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ : Concentration S} {K : Set (Concentration S)}
    (hKc : IsClosed K) (hKpos : ∀ y ∈ K, y.Positive)
    {v : Set ℝ≥0} (hv : v ∈ (atTop : Filter ℝ≥0))
    (hvK : closure (Set.image2 ϕ v {x₀}) ⊆ K) :
    ∀ y ∈ omegaLimit atTop ϕ {x₀}, y.Positive := by
  intro y hy
  exact hKpos y (hvK ((omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀})
    hv) hy))

omit [DecidableEq S] [Fintype S] in
/-- **The `False`-form: a route that exhibits a single closed positive confine produces a
contradiction, not the conclusion.**

This is the corollary to reach for when you try to close Hole A by exhibiting one floored,
closed trapping region and handing it to a packaged criterion. Doing so does not fail to
suffice — it *yields `False`*, and Lean will point you here rather than leaving you with a
`sorry` and no diagnosis.

It is deliberately stated in the shape a caller would supply, so the failing attempt matches
a hypothesis rather than a pattern: `hwmax`, `hPmaxne`, `hzeroMax` are exactly the hole's. -/
theorem false_of_closedPositiveConfine_and_boundaryOmegaPoint
    {ϕ : Flow ℝ≥0 (Concentration S)} {x₀ wmax : Concentration S} {K : Set (Concentration S)}
    (hKc : IsClosed K) (hKpos : ∀ y ∈ K, y.Positive)
    {v : Set ℝ≥0} (hv : v ∈ (atTop : Filter ℝ≥0))
    (hvK : closure (Set.image2 ϕ v {x₀}) ⊆ K)
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    (hzeroMax : ∀ (s : S), s ∈ Pmax ↔ wmax s = 0) :
    False := by
  have hall := universalPositive_omegaLimit_of_closedPositiveConfine
    (ϕ := ϕ) (x₀ := x₀) (K := K) hKc hKpos hv hvK wmax hwmax
  obtain ⟨s₀, hs₀⟩ := hPmaxne
  exact (hall s₀).ne' ((hzeroMax s₀).mp hs₀)

omit [DecidableEq S] in
/-- **Closedness of the Horn–Jackson sublevel set on the nonnegative orthant.**

`isClosed_le (relEntropy_continuous hxs) _` closes the *bare* level set
`{y | relEntropy xstar y ≤ C}`; the confining set a criterion actually builds is
`{y | y.Nonnegative ∧ relEntropy xstar y ≤ C}`, which needs the nonnegative conjunct closed as
well. `isCompact_relEntropy_sublevel` (`CRNT/Theorems/DeficiencyZero/AsymptoticStability.lean:142`)
proves the compactness of that intersection inline and does not expose this step, so every
caller that wants to apply `universalPositive_omegaLimit_of_closedPositiveConfine` to it has
to re-derive it. Naming it here removes that repetition. -/
theorem isClosed_relEntropy_sublevel_nonneg {xstar : Concentration S} (hxs : xstar.Positive)
    (C : ℝ) :
    IsClosed {y : Concentration S | y.Nonnegative ∧ relEntropy xstar y ≤ C} := by
  have hnn : IsClosed {y : Concentration S | y.Nonnegative} := by
    have heq : {y : Concentration S | y.Nonnegative} = ⋂ s, {y : Concentration S | 0 ≤ y s} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_iInter]; rfl
    rw [heq]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  exact hnn.inter (isClosed_le (relEntropy_continuous hxs) continuous_const)

end Network
end CRNT