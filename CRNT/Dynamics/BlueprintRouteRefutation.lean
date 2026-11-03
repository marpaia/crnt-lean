import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Dynamics.ToricBarrierExplicit
import CRNT.Dynamics.OrbitRegularity

/-!
# The packaged barrier route is refutable under the hypotheses of hole A

`CRNT/Dynamics/HighCodimensionSiphonFace.lean` records, in prose, that the packaged blueprint
criteria (`exists_positive_omegaPoint_of_blueprintData`, `…_of_selfConsistent_normals`,
`…_of_convex_tiles`, `…_of_toric_blueprint`, `…_of_tiled_faceCores`,
`…_of_faceRelevantCore`) *cannot* be instantiated from the hypotheses of
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`: the separation clause `hsep`
they all demand is refuted by the boundary ω-point `wmax`.  The two lemmas
`Network.hsep_fails_of_boundaryPoint_mem_sublevel` and
`Network.barrier_le_of_mem_omegaLimit` are the machine-checked core of that analysis, but the
module states plainly that

> "the wiring to each criterion's hypotheses is the paragraph above",

i.e. the composition was never checked.  This module checks it.

## What is proved

1. `floor_on_omegaLimit_of_floor_along_orbit` — a **barrier-free** fact.  A uniform coordinate
   floor along the forward orbit forces the same floor on every ω-limit point.  No barrier, no
   polyhedron, no fan, no `N`, no `κ`.

2. `no_uniform_floor_along_orbit_of_boundaryOmegaPoint` — the consequence.  If `w` is an ω-limit
   point vanishing at `s`, then there is no `ε > 0` with `ε ≤ γ x₀ t s` for all `t ≥ 0`.

3. `not_separationClause_of_boundaryOmegaPoint` — the barrier wiring: `hstart` plus trapping plus
   one boundary ω-point refutes `hsep`, in exactly the shape
   `exists_positive_omegaPoint_of_convex_tiles` and `…_of_selfConsistent_normals` demand.

4. `blueprintData_inconsistent_with_highCodimension` — **the full refutation.**  Every hypothesis
   of `Network.exists_positive_omegaPoint_of_blueprintData`, together with the ω-limit hypotheses of
   hole A, are jointly inconsistent: the theorem concludes `False`.

Every rung of the ladder in `CRNT/Dynamics/FaceDirectionCone.lean` and
`CRNT/Dynamics/ToricBarrierTrapping.lean` terminates in
`Network.exists_positive_omegaPoint_of_coordinate_floors` with the species set `T = S`, so (2)
alone kills all of them, including the `minMaxBarrier` rungs.

## Consequence for the swarm

Hole A cannot be closed by a route whose conclusion flows through a uniform coordinate floor.  The
live target is `Network.exists_positive_omegaPoint_of_upperRegion`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:1596`), whose floor hypothesis is conditioned on
staying in a region `Zupper` rather than quantified over the whole compatibility class, and which
none of (1)–(4) touches.

Section 4 gives the weakened separation statement that *is* satisfiable: floors on a subset of the
species, giving an ω-limit point in the relative interior of a coordinate face.

Nothing here imports `CRNT.Dynamics.GlobalAttractorTheorem`, which sits on the frontier ledger.
There is no axiom and no `sorry` in this file.

Depends on: `CRNT.Dynamics.HighCodimensionSiphonFace`, `CRNT.Dynamics.ToricBarrierExplicit`.
-/

open Filter
open scoped NNReal Topology RealInnerProductSpace

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] [Nonempty S]

/-! ### 1. The barrier-free obstruction: uniform floors along the orbit -/

/-- **A uniform coordinate floor along the forward orbit forces the same floor on every ω-limit
point.**  The orbit lies in the closed set `{y | ε ≤ y s}`; that set is closed, so its closure
does; and every ω-limit point lies in the closure of the forward orbit. -/
theorem floor_on_omegaLimit_of_floor_along_orbit
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {ε : ℝ} (hε : 0 < ε) {s : S}
    (hfloor : ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t s) (z : Concentration S)
    (hz : z ∈ omegaLimit atTop ϕ {x₀}) : ε ≤ z s := by
  have hclosed : IsClosed {y : Concentration S | ε ≤ y s} :=
    isClosed_Ici.preimage (continuous_apply s)
  have horbit : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ {y : Concentration S | ε ≤ y s} := by
    rintro y ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hϕγ]
    exact hfloor t t.coe_nonneg
  have hω : omegaLimit atTop ϕ {x₀} ⊆ {y : Concentration S | ε ≤ y s} :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr horbit)
  exact hω hz

/-- **No uniform coordinate floor along the orbit can coexist with a boundary ω-point.**

This is the obstruction that kills every floor-based criterion for hole A, independently of any
barrier, any fan cone, or any polyhedral geometry: if `w` is an ω-limit point vanishing at `s`,
then some forward time has `γ x₀ t s < ε` for every `ε > 0`.

Together with `exists_positive_omegaPoint_of_coordinate_floors` this says the floor-based toolkit
and hole A's ω-limit hypotheses are jointly unsatisfiable. -/
theorem no_uniform_floor_along_orbit_of_boundaryOmegaPoint
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {w : Concentration S} {s : S}
    (hw : w ∈ omegaLimit atTop ϕ {x₀}) (hsw : w s = 0) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t s := by
  rintro ⟨ε, hε, hfloor⟩
  have h := floor_on_omegaLimit_of_floor_along_orbit hϕγ hK hmaps hε hfloor w hw
  rw [hsw] at h
  exact lt_irrefl 0 (lt_of_lt_of_le hε h)

/-! ### 2. The separation clause is refuted by the guarded region -/

variable {ι' : Type} [Fintype ι'] [Nonempty ι']

/-- **The separation clause `hsep` of the packaged barrier criteria is refuted by `hstart`,
trapping, and a boundary ω-point.**

`hstart` puts `x₀` in the closed sublevel; `htrap` puts the whole forward orbit there;
`Network.barrier_le_of_mem_omegaLimit` therefore puts `wmax` there too.  The sublevel is convex,
so the segment from `x₀` to `wmax` stays in it, and at a coordinate where `wmax` vanishes that
segment takes the value `x₀ s / n → 0`.  `hcompat` supplies the compatibility of `wmax` with `x₀`.

This is the wiring the `HighCodimensionSiphonFace` packaging audit leaves as prose. -/
theorem not_separationClause_of_boundaryOmegaPoint
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ wmax : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (N : Network S) (m : ι' → N.euclideanStoichSubspace) (b : ι' → ℝ) (R : ℝ)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) ≤ R)
    (htrap : ∀ t : ℝ, 0 ≤ t →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R)
    (hx₀ : x₀.Positive)
    (hwnn : Concentration.Nonnegative wmax)
    (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hcompat : N.StoichCompatible x₀ wmax)
    {s : S} (hsw : wmax s = 0) :
    ¬ ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
        N.StoichCompatible x₀ x →
        PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
          (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
  intro hsep
  have hbar : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState wmax) ≤ R :=
    barrier_le_of_mem_omegaLimit N m b R hϕγ htrap hwmax
  exact (hsep_fails_of_boundaryPoint_mem_sublevel N m b R
    hx₀ hwnn hcompat hsw hstart hbar) (hsep s)

/-! ### 3. The full refutation of the packaged route -/

/-- **The packaged blueprint data and the ω-limit hypotheses of hole A are jointly
inconsistent.**

This takes *exactly* the hypotheses of
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` (only `hωnn`, `hωaff` and the
`wmax` clauses are used; `hgenω`, `hmaxExact`, `hzcard`, `hcodim`, `hcard`, `hrank` are not needed)
together with *exactly* the hypotheses of
`Network.exists_positive_omegaPoint_of_blueprintData`, and derives `False`.

Hence the packaged criteria cannot be instantiated from hole A's hypotheses: applying one would
derive `False` rather than the conclusion, so the criterion would be discharging a hypothesis set
that no network with a boundary ω-point can satisfy.  Any proof of hole A along this route is a
proof of `False`. -/
theorem blueprintData_inconsistent_with_highCodimension
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    {δ : ℝ} (hδ : 0 < δ) {P : Finset S} {B R R' M : ℝ} (hRR' : R < R')
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ}
    (piece : S → ι')
    (hMclass : ∀ x : Concentration S, x.Positive → N.StoichCompatible (γ x₀ 0) x →
      ∀ u, x u ≤ M)
    (hpos : ∀ s : S, 0 < ((m (piece s) : EuclideanSpace ℝ S) s))
    (hlevel : ∀ s : S,
      M * (∑ u ∈ Finset.univ.erase s, max ((m (piece s) : EuclideanSpace ℝ S) u) 0)
        < -(R + b (piece s)))
    (hm : ∀ i : ι', ∀ C ∈ N.relevantCones (N.activeFaceImage P xstar (γ x₀) m b R R' i) δ B,
      m i ∈ C)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState (γ x₀ 0)) ≤ R)
    (hregime : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B) :
    False := by
  -- the orbit starts at `x₀`
  have hγ0 : γ x₀ 0 = x₀ := by
    have h := hϕγ x₀ 0
    simpa using h.symm
  -- a uniform coordinate ceiling on the compact `K`, hence along the orbit
  have hKne : K.Nonempty := ⟨ϕ 0 x₀, hmaps 0⟩
  obtain ⟨Bx, hBx⟩ : ∃ Bx : ℝ, ∀ y ∈ K, ∀ s, y s ≤ Bx := by
    have hco : ∀ s : S, ∃ c : ℝ, ∀ y ∈ K, y s ≤ c := by
      intro s
      obtain ⟨z, hzK, hz⟩ := hK.exists_isMaxOn hKne (continuous_apply s).continuousOn
      exact ⟨z s, fun y hy => hz hy⟩
    choose c hc using hco
    exact ⟨Finset.univ.sup' Finset.univ_nonempty c, fun y hy s =>
      le_trans (hc s y hy) (Finset.le_sup' c (Finset.mem_univ s))⟩
  have hΓbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ x₀ t s ≤ Bx := by
    intro t ht s
    have hmem : γ x₀ t ∈ K := by
      have h := hmaps ⟨t, ht⟩
      rw [hϕγ x₀ ⟨t, ht⟩] at h
      exact (show ((⟨t, ht⟩ : ℝ≥0) : ℝ) = t from rfl) ▸ h
    exact hBx _ hmem s
  -- the three orbit bridges, exactly as in `docs/gac-bridge-gap-analysis.lean`
  have hΓcont : ContinuousOn (γ x₀) (Set.Ici 0) := fun t ht =>
    ((hsol t ht).continuousAt).continuousWithinAt
  have hΓpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive :=
    N.orbit_pos_forward κ (by rw [hγ0]; exact hx₀) hΓbdd hsol
  have hclass : ∀ t, 0 ≤ t → N.StoichCompatible (γ x₀ 0) (γ x₀ t) :=
    N.stoichCompatible_of_forward_solution κ hsol
  -- the fan clause `hnear`, assembled from `hm`, `activeFaceImage` and `hregime`
  have hnear : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ∀ i : ι',
        innerSL ℝ (-m i) (N.euclideanStoichState (γ x₀ t)) - b i
          = PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
              (N.euclideanStoichState (γ x₀ t)) →
        ∀ C ∈ N.relativeSourceOrderNegativeStoichFan,
          Metric.infDist (N.relativeLogFanState xstar (γ x₀ t))
            (C : Set N.euclideanStoichSubspace) < δ → m i ∈ C := by
    intro t ht hlev hband i hactive C hCF hCnear
    exact hm i C
      (N.mem_relevantCones_of_infDist_lt P
        (N.faceLogPart_mem_activeFaceImage P ht hlev hband hactive)
        (hregime t ht hlev hband) hCF hCnear)
  -- trapping along the whole orbit
  have hstart0 : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x₀) ≤ R := by rw [← hγ0]; exact hstart
  have hstartΓ : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ 0)) ≤ R := hstart
  have htrap : ∀ t : ℝ, 0 ≤ t →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R :=
    N.barrier_le_of_toric_descent_in_band κ hxs hcb hδ hRR' hΓcont hΓpos hsol hstartΓ hnear
  -- `hsep`, discharged internally by the packaged criterion from `hMclass`/`hpos`/`hlevel`
  have hsep : ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
      N.StoichCompatible (γ x₀ 0) x →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
    intro s
    obtain ⟨ε, hε, hbound⟩ :=
      N.coordinate_floor_of_dominant_barrier (M := M) (R := R) (b := b) piece hpos hlevel s
    exact ⟨ε, hε, fun x hxpos hxclass hxregion =>
      hbound x (fun u => (hxpos u).le) (fun u => hMclass x hxpos hxclass u) hxregion⟩
  -- the same clause with `x₀` in place of `γ x₀ 0`, which is what the refutation consumes
  have hsep0 : ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
      N.StoichCompatible x₀ x →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
    intro s
    obtain ⟨ε, hε, hbound⟩ := hsep s
    refine ⟨ε, hε, fun x hxpos hxclass hxregion => ?_⟩
    have hxclass' : N.StoichCompatible (γ x₀ 0) x := by rw [hγ0]; exact hxclass
    exact hbound x hxpos hxclass' hxregion
  -- `wmax` is compatible with `x₀` and vanishes somewhere on `Pmax`
  have hcompat0 : N.StoichCompatible x₀ wmax := hωaff wmax hwmax
  obtain ⟨s₀, hs₀⟩ := hPmaxne
  have hsw0 : wmax s₀ = 0 := (hzeroMax s₀).mp hs₀
  -- the contradiction
  exact (not_separationClause_of_boundaryOmegaPoint hϕγ N m b R
    hstart0 htrap hx₀ (hωnn wmax hwmax) hwmax hcompat0 hsw0) hsep0

/-! ### 4. The weakened target: floors off the boundary face, not on all of `S`

Craciun's ZSH Definition 4.6(i) demands η-separation from *every* coordinate hyperplane.  The
hole's conclusion does not: it asks for one strictly positive ω-limit point.  The distinction is
exactly the distinction between the refutations above and what follows.

`exists_positive_omegaPoint_of_coordinate_floors` asks for a floor on *every* species.  A floor on
each species of a finset `T ⊆ S` already forces the ω-limit set to meet
`{y | ∀ s ∈ T, ε s ≤ y s}`, a **relatively open** part of the `T`-face.  Nothing here is a uniform
floor over all of `S`, so nothing here collides with a boundary ω-point that vanishes on `S \ T`. -/

/-- **Floors on a subset `T` of the species give an ω-limit point positive on `T`.**

This is `Network.exists_positive_omegaPoint_of_coordinate_floors` with the quantification over `S`
restricted to a finset `T`.  The orbit lies in the closed set `{y | ∀ s ∈ T, ε s ≤ y s}`, so its
closure does, so every ω-limit point does.  No hypothesis is placed on the species outside `T`.

This is the weakened separation clause of the reframe: every packaged criterion demands the same
statement with `T = S`, and `no_uniform_floor_along_orbit_of_boundaryOmegaPoint` refutes that.
With `T` a proper subset the statement is consistent. -/
theorem exists_omegaPoint_positive_on_of_floors_on
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {T : Finset S}
    (hlower : ∀ s ∈ T, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t s) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, ∀ s ∈ T, 0 < p s := by
  have hsubK : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆ K := by
    rintro z ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hmaps t
  have habs : ∃ v ∈ (atTop : Filter ℝ≥0), closure (Set.image2 ϕ v {x₀}) ⊆ K :=
    ⟨Set.univ, univ_mem, (hK.isClosed.closure_subset_iff).mpr hsubK⟩
  obtain ⟨p, hp⟩ :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x₀} hK habs (Set.singleton_nonempty x₀)
  refine ⟨p, hp, fun s hs => ?_⟩
  obtain ⟨ε, hε, hfloor⟩ := hlower s hs
  have hclosed : IsClosed {y : Concentration S | ε ≤ y s} :=
    isClosed_Ici.preimage (continuous_apply s)
  have horbit : Set.image2 ϕ (Set.univ : Set ℝ≥0) {x₀} ⊆
      {y : Concentration S | ε ≤ y s} := by
    rintro y ⟨t, -, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [hϕγ]
    exact hfloor t t.coe_nonneg
  have hω : omegaLimit atTop ϕ {x₀} ⊆ {y : Concentration S | ε ≤ y s} :=
    (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {x₀}) (u := Set.univ)
      univ_mem).trans ((IsClosed.closure_subset_iff hclosed).mpr horbit)
  exact lt_of_lt_of_le hε (hω hp)

/-- **Floors off a finset `P` give an ω-limit point in the relative interior of the `P`-face.**

Take `T := (Finset.univ \ P : Finset S)`: the ω-limit point returned is strictly positive at every species
outside `P`, i.e. it lies in the relative interior of the coordinate face `{y | ∀ s ∈ P, y s = 0}`
— the Anderson–Shiu "locally persistent relative-interior point".

This is a surviving, satisfiable target for hole A.  It is strictly weaker than the conclusion
`exists_positive_omegaPoint_of_highCodimension_siphonFace` demands (it says nothing about the
coordinates in `P`), and it is not refuted by §1–§3, because those need a floor at a species some
ω-limit point vanishes at, and no species of `(Finset.univ \ P : Finset S)` is such a species. -/
theorem exists_positive_omegaPoint_of_relInteriorFace
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    {P : Finset S}
    (hlower : ∀ (s : S), s ∈ (Finset.univ \ P : Finset S) →
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 ≤ t → ε ≤ γ x₀ t s) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, ∀ (s : S), s ∈ (Finset.univ \ P : Finset S) → 0 < p s := by
  exact exists_omegaPoint_positive_on_of_floors_on (T := (Finset.univ \ P : Finset S)) hϕγ hK hmaps hlower

/-! ### 5. The Step-4 criterion: refuted elsewhere, not duplicated here

`Network.exists_positive_omegaPoint_of_upperRegion`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean:1596`) is refuted: the criterion builds a **closed**
`K := closure Zupper ∩ {relEntropy ≤ relEntropy x₀}` containing the whole orbit image (`himgs`), so
`omegaLimit ⊆ K` is forced; `hKpos` at `:1629` is **universal** (`∀ y ∈ K, y.Positive`), so
`wmax ∈ ω ⊆ K` is forced strictly positive, contradicting `hzeroMax` + `hPmaxne`.  Its `hfloor` is
not an unbuilt input; it is an **inconsistent** one.

The canonical statement is `CRNT.Network.universalPositive_omegaLimit_of_closedPositiveConfine`
(branch `research/infrascaffold`), and the criterion-level `False` is
`false_of_upperRegion_and_boundaryOmegaPoint` in
`CRNT/Dynamics/UpperRegionFloorRefutation.lean` on the same branch.  Both are deliberately **not
duplicated here**: four copies of one `False`-level theorem is worse than one, because a reviewer
has to check four.

**Known gap in the canonical statement, for whoever consolidates.**  It takes the closed
confinement as a *hypothesis* (`hvK : closure (Set.image2 ϕ v {x₀}) ⊆ K`).  Retiring the *packaged
criterion* additionally needs the confinement **derived from the criterion's own hypotheses**,
i.e. `Network.orbit_stays_in_upperRegion` (`HighCodimensionSiphonFace.lean:1508`) applied to
`hsplit`, `hopenLow`, `hopenUp`, `hdisj`, `hx₀Z` — connectivity of `γ '' Ici 0` plus the disjoint
open split — to obtain `γ x₀ t ∈ Zupper`, whence the orbit image lies in `closure Zupper ⊆ K`.  I
had that as `upperRegion_criterion_inconsistent_with_boundaryOmegaPoint` and have removed it here
per the consolidation decision; the derivation is a three-line corollary to restore on top of the
canonical theorem.  It is the statement that actually answers "are `_of_upperRegion`'s own
hypotheses satisfiable under the hole's?". -/

end Network
end CRNT