# BRIEF A — Craciun v3 Theorem B: the codimension ≥ 2 zero-separating surface

## A.1 The target

`CRNT/Dynamics/HighCodimensionSiphonFace.lean:135`

```lean
theorem Network.exists_positive_omegaPoint_of_highCodimension_siphonFace
    (N : Network S) (κ : N.RateConstants)
    {xstar} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S} {x₀}
    (hϕγ : ∀ x t, ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K} (hK : IsCompact K) (hmaps : ∀ t, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hrank : N.stoichRank ≠ 1) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive
```

> **Correction (round 1).** The Craciun v3 reference above originally read "arXiv:2306.03055".
> That is wrong — arXiv:2306.03055 is an NLP paper on Japanese honorific conversion. The correct
> identifier is **arXiv:1501.02860**, G. Craciun, *Toric Differential Inclusions and a Proof of the
> Global Attractor Conjecture*, v3. The repository was already right:
> `docs/persistence-gac.md:283` and `:300` cite `arxiv.org/html/1501.02860v3`.

> **Accessibility warning, verified round 1.** The arXiv LaTeXML HTML at
> `arxiv.org/html/1501.02860v3` is **truncated**: it ends mid-sentence in §6.1.1 and contains
> **no §7, §8 or §9 at all** — precisely the material hole A needs. Anyone relying on the HTML
> silently loses the entire construction. The **PDF** (`arxiv.org/pdf/1501.02860v3`, 91 pages) is
> complete and must be used instead.
>
> **Figures are a hard blocker for parts of §5–§6.** The constructions in §5, §6.1.1 and §6.2.1
> are specified largely *by figure reference*. Figure content is not machine-extractable, so the
> numeric blueprint data (specific ε values, the red dot placements, face enumerations) is **not
> recoverable from text alone**. Any route that needs those numbers must either reconstruct them or
> go through §7, which is textual.

Downstream: `Network.complexBalanced_genuinePermanent` → `complexBalanced_permanent` →
`complexBalanced_globalAttractor`. `#print axioms` on all four currently reports `sorryAx`.
This theorem is the **entire** residual content of the Global Attractor Conjecture as formalized here.

## A.2 What is already proved (do not re-derive)

Everything except the `hcodim`-branch is closed. In particular:

* the dichotomy `positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium`;
* `exists_maximal_zeroSet_omegaPoint` — the `wmax` / `Pmax` package above;
* `CRNT.Dynamics.FaceCodimension.highCodimension_of_not_facet` — supplies `hcodim`, `hcard`;
* the facet branch: `facet_repelling_near_facet_point` + `no_omegaLimit_meets_locally_repelling_face`,
  i.e. codimension 1 is fully closed via the Anderson–Shiu estimate;
* `CRNT.Dynamics.FaceCodimension`, `CRNT.Dynamics.SiphonDimensionDescent`,
  `CRNT.Dynamics.ToricBarrierTrapping`, `CRNT.Dynamics.SingleLinkageGAC`;
* `CRNT.Geometry.PolyhedralBarrier` — **the invariance engine**: for
  `g X = max i (⟪n i, X⟫ − b i)` the sublevel set `{g ≤ R}` is forward invariant for any field
  lying in the polar cones of the active normals. This is fully proved and is the consumer's job;
* `Network.exists_positive_omegaPoint_of_blueprintData`, `…_of_convex_tiles`,
  `…_of_selfConsistent_normals`, `…_of_toric_blueprint`, `…_of_toric_halfspace`,
  `…_of_faceRelevantCore`, `…_of_tiled_faceCores` — the whole downstream consumer chain, proved;
* `docs/gac-bridge-gap-analysis.lean` — **proves that the residual obligation follows from the
  blueprint data alone**, with no `sorry` and no errors, discharging all three
  orbit-level bridges (`ContinuousOn`, positivity, stoichiometric compatibility) from the residual's
  own hypotheses. Read it; it is the exact shape of the remaining work.

## A.3 The single missing object

> **The existence of the blueprint data for an arbitrary complete pointed fan.**

Concretely: for a complete pointed polyhedral fan in `ℝ^d` with cone set `C`, produce a family
`n C ∈ C` indexed by the cones, satisfying

* **self-consistency / dominance:** `⟪n C, x⟫ ≥ ⟪n C', x⟫` for every `x ∈ C` and every cone `C'`;
* **separation scales:** an associated set of `δ`-values obeying the scale hierarchy of Craciun v3 §7;
* **tile data:** a finite covering of each cone by compact projective tiles with the projection
  and seam-agreement data needed by the consumer chain;
* **depth/termination:** the recursive face-fill strictly decreases rank.

This is Theorem B of Craciun, *Toric differential inclusions and a proof of the global attractor
conjecture*, arXiv:2306.03055v3 — equivalently the "exhaustive family of zero-separating
hypersurfaces" whose outer normal at `X` lies in **every** cone of the fan within distance `δ` of
`X` (Lemma 9.5, and Lemma 9.7 with the `δ`-slack).

## A.4 Known dead ends — do not re-walk these

* **Pushing Anderson–Shiu to codimension ≥ 2.** `facet_repelling_near_facet_point` needs every
  reaction vector restricted to `Pmax` to be a multiple of one direction `v`, i.e. exactly
  `finrank (stoichSubspace.map (projOn Pmax)) = 1`. Under `hcodim` the restricted reaction vectors
  span a plane and `∑_{s ∈ Pmax} (x s)^2` is *not* monotone near `wmax`: with `x s = ε u s`,
  the leading term is a quadratic form in `u ≥ 0` whose sign varies — for a reversible pair inside
  the face with equal rate constants it is a negative multiple of a square. A smooth surface
  cannot satisfy the `δ = 0` condition of Lemma 9.5 while failing Lemma 9.7. **Polyhedral is
  forced.**
* **Instantiating a packaged criterion directly from this theorem's hypotheses.** Recorded in
  `docs/gac-bridge-gap-analysis.md`: the packaged criteria *cannot* be instantiated here; the
  blueprint data does not exist under `hcodim`. The two lemmas in
  `HighCodimensionSiphonFace.lean` after line 140 record this obstruction — read them.
* **A globally smooth surface.** Local smooth-max tile witnesses do not assemble. The failure is
  coherence across the face lattice, not existence of local pieces.

## A.5 Where the real difficulty is, ranked

1. **No polytope / face-lattice / normal-fan API in Mathlib.** `docs/gac-v3-face-fill-plan.md` names
   this as the reason the face-point family was never built. Tier C must supply this: finitely
   generated polyhedral cones, faces, incidence, normal cones, and the "a polytope whose normal fan
   refines `C`" construction. This is the #1 blocker and the highest-leverage work in the swarm.
2. **Recursive face-fill with a rank-decreasing invariant** (Craciun v3 §7.4.3 Cases 1.1/1.2, Step 2).
   `FanRefinement` has the *local* data (common faces, rank drops);
   `ZeroSeparatingInduction` has the binary-word scales and fiber boxes; what is missing is the
   coherent recursive assembly.
3. **The `δ`-slack bookkeeping** of Lemma 9.7 — a quantitative statement about how far a normal may
   stray, and how the scale hierarchy propagates it.

## A.6 What a completed Hole A looks like

* `exists_positive_omegaPoint_of_highCodimension_siphonFace` has no `sorry`.
* `#print axioms Network.complexBalanced_globalAttractor` reports only
  `[propext, Classical.choice, Quot.sound]`.
* `CRNT/Dynamics/HighCodimensionSiphonFace.lean` drops off `scripts/unverified_modules.txt`,
  `lake build CRNT` is green, and `scripts/check_exclusions.py` still passes.