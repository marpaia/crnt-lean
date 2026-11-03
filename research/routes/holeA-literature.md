# Hole A against the published GAC case list

Read the primary source this session: **G. Craciun, *Toric Differential Inclusions and a Proof of the
Global Attractor Conjecture*, arXiv:1501.02860v3** (fetched via `read` on `/pdf/1501.02860`; 91pp,
complete — the alphaxiv detour in DEAD-ENDS A-15 is unnecessary).

Everything marked `[SOURCED]` is quoted from that PDF.

## 1. The published case list, verbatim

§1, `[SOURCED]`:

> "The conjecture … has resisted efforts for a proof for over five decades, but proofs of many
> special cases have been obtained during this time … In particular, **Craciun, Nazarov and Pantea
> [3] have proved the three-dimensional case, and Pantea has generalized this result for the case
> where the dimension of the linear invariant subspaces is at most three** [18]. Using a different
> approach, **Anderson has proved the conjecture under the additional hypothesis that the graph G
> has a single connected component** [5], and this result has been **generalized by
> Gopalkrishnan, Miller, and Shiu for the case where G is strongly endotactic** [15]."

And it explicitly lists what the paper itself does **not** cover `[SOURCED]`:

> "The results described above do not provide a proof of the global attractor conjecture in full
> generality, and also do not provide a proof for any of the following three important special
> cases: *(i)* the case where *G* is **reversible**, *(ii)* … reversible and **detailed balanced**,
> and *(iii)* … reversible and *k*<sub>y→y′</sub> = *k*<sub>y′→y</sub>."

**Terminology correction relevant to the repo.** "single connected component" of `G` is the
single-**linkage**-class condition, i.e. `N.numLinkageClasses = 1`. DEAD-ENDS A-57/A-63 are
therefore **confirmed correct** by the primary source: under ℓ=1 Anderson's result gives "every ω-point
is positive", which contradicts the hole's own `hwmax`. So the hole's hypotheses are *inconsistent*
under ℓ=1, and that route stays closed. `[SOURCED]`

## 2. "strongly endotactic" is a published GAC case, and the repo already models it

The Gopalkrishnan–Miller–Shiu generalization is cited by Craciun as a case where **the full GAC
holds** (not merely persistence). The repo has a substantial endotactic development:

- `CRNT/Geometry/EndotacticGlobal.lean`
- `N.Endotactic`, `N.StronglyEndotacticStd`
  (`CRNT/Dynamics/TierDirectionProjection.lean:342`, `:347`;
  `CRNT/Dynamics/TierPersistence.lean:168`, `:197`, `:215`, `:457`)
- `StrongEndotacticCertificate` (`CRNT/Dynamics/GlobalPersistenceCertificates.lean:198`)

**This is the hypothesis the repo has never matched against `HighCodimensionSiphonFace.lean`'s
twenty hypotheses.** `hcodim` is `2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax))` and
`hrank : N.stoichRank ≠ 1` — neither is an endotacticity hypothesis, and nothing in
`:111-133` mentions endotacticity. So the GMS case does not cover the hole either. But it is now a
**named, citable alternative** rather than an unnamed "maybe some literature case applies", and it
belongs in the ledger as a route that was never evaluated rather than one assumed unavailable.

## 3. The in-tree interfaces already match the literature

`CRNT/Dynamics/KnownGlobalPersistenceClasses.lean` (94 lines) records the published cases as Lean
interfaces, and its docstring states `[SOURCED]`-equivalent policy:

> "No proposition in this file is an axiom: downstream code must receive a proof before using it."

| interface | line | published counterpart |
|---|---|---|
| `TwoDimensionalWRBoundedPersistenceClaim` | 52 | Pantea, dim of linear invariant subspace ≤ 3, rank 2 |
| `TwoSpeciesEndotacticPermanenceClaim` | 58 | CNP two-*species* endotactic |
| `TwoSpeciesWRPermanenceClaim` | 63 | derived from the above (`twoSpeciesWRPermanence_of_endotacticPermanence`, `:67`) |
| `IsFirstOrder` / `FirstOrderEndotacticPersistenceClaim` | 84, 90 | 2026 first-order endotactic global-stability |

**Crucially, `Pantea` is the closest published result to the hole, and it is keyed on
`N.stoichRank = 2`.** The hole carries `hrank : N.stoichRank ≠ 1`, i.e. rank ≥ 2 — so **the rank-2
sub-case of the hole is covered by a published theorem that is already sitting in the tree as an
unproved interface.**

## 4. The concrete new route this unlocks — the only one the literature suggests

Split the hole on `hcodim`/rank and try to consume `TwoDimensionalWRBoundedPersistenceClaim`:

- **rank = 2 case:** supply `N.WeaklyReversible` and `N.StructurallyBoundedPositiveTrajectories`.
  The latter is *almost* free here: the hole already has `hK`/`hmaps` for one trajectory, and
  `N.StructurallyBoundedPositiveTrajectories` quantifies over **all** `κ` and **all** `x₀`
  (`:46-48`), which is strictly more than the hole has. So this needs the boundedness upgrade, not
  the endotacticity hypothesis.
  **Caveat that may kill it:** the theorem concludes `N.StructurallyPersistentStd`, i.e. *every* ω-point
  positive — which under the hole's `hwmax`/`hzeroMax`/`hPmaxne` is `False`, not the hole's goal
  (DEAD-ENDS A-19's "universal vs existential" point). It would close the hole **by refutation of
  its hypotheses**, i.e. by proving `¬` the conjunction. That is a legitimate `False`-production
  only if the upgraded hypotheses are genuinely available; if they are not, this route is dead in
  the same way `PersistentFrom` was (A-18/A-19).
- **weak reversibility:** the hole does **not** assume it. `N.WeaklyReversible` is not among
  `:111-133`. Complex-balanced does **not** imply it (a positive complex-balanced equilibrium need
  not come from a weakly reversible network). So this case is likely closed too, and needs an
  explicit check rather than an assumption.

**Honest status: this narrows the search but does not open a route.** What it establishes is that
the hole sits in the case Craciun explicitly leaves to §8 ("Proof of the global attractor conjecture
in the *n*-dimensional case", p. 77), and that the two nearest published theorems are (a) keyed on
rank 2 + weak reversibility, neither available, and (b) keyed on strong endotacticity, which the hole
neither assumes nor is implied by.

## 5. What is *not* answered

Craciun's own §5 (2D), §6 (3D), §7 (subdivisions/blueprints), §8 (n-dimensional) are the general
construction. The hole's codim-≥2 face case is not separately treated anywhere in the paper — it is
absorbed into the general blueprint argument. **So no published shortcut exists for the hole's exact
configuration**, and DEAD-ENDS A-1/A-2/A-12/A-65 (the blueprint recursors rank the wrong quantity;
`binaryWordValue` is anti-monotone; Lemma 9.7 has no quantitative slack; the fan cannot serve the
descent) stand unrefuted by anything in the primary source.

## 6. Cited sources
- G. Craciun, *Toric Differential Inclusions and a Proof of the Global Attractor Conjecture*,
  arXiv:1501.02860v3, §1 (case list), §4 (Steps 0–4 plan), §7, §8. `[SOURCED]`
- D. F. Anderson, *A proof of the global attractor conjecture in the single linkage class case*,
  SIAM J. Appl. Math. **71**(4): 1487–1508, 2011 — confirms ℓ=1 route (DEAD-ENDS A-57/A-63).
- M. Pantea, generalization to dimension ≤ 3 of the linear invariant subspace — recorded in-tree as
  `TwoDimensionalWRBoundedPersistenceClaim`.
- M. Gopalkrishnan, E. Miller, Z. Shiu, strongly endotactic case — **not represented in-tree as a GAC
  interface**; the repo has `StrongEndotacticStd` but not the GAC conclusion. Candidate for the
  frontier ledger.

## 7. CORRECTION to §4 — the hole DOES have weak reversibility; the rank-2 route reopens

§4 asserted the Pantea route "likely dies" because the hole does not assume `N.WeaklyReversible`.
**That is wrong**, and the correction reopens the route.

`CRNT/Equilibria/ComplexBalanceStructure.lean:39-45`, verbatim:

```lean
/-- **Positive complex balance forces weak reversibility.** -/
theorem weaklyReversible_of_positive_complexBalanced
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hcb : N.IsComplexBalanced κ x) :
    N.WeaklyReversible := by
  exact N.weaklyReversible_of_exists_pos_kernelVector κ
    (N.complexMonomialVector_pos hx)
    (N.kineticMap_complexMonomial_eq_zero_of_complexBalanced κ hcb)
```

The hole's hypotheses `hxs : xstar.Positive` and `hcb : N.IsComplexBalanced κ xstar` at
`HighCodimensionSiphonFace.lean:113` are **exactly** this lemma's two arguments. So

```lean
have hwr : N.WeaklyReversible :=
  N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
```

is available **in the hole, for free**. Verified by reading the source; and
`no_positive_complexBalanced_of_not_weaklyReversible` (`:50-56`) is the same fact's contrapositive,
which is why the grep for "CB ⇒ WR" initially returned only reverse-looking hits.

I had this backwards because I assumed, following the general literature convention, that
complex-balanced and weakly-reversible are independent. **In this library that convention is not
followed**: here positive complex balance *implies* weak reversibility as a proved theorem.

### Revised status of the Pantea / rank-2 route

`TwoDimensionalWRBoundedPersistenceClaim` (`KnownGlobalPersistenceClasses.lean:52`) is

```lean
def TwoDimensionalWRBoundedPersistenceClaim (N : Network S) : Prop :=
  N.WeaklyReversible → N.stoichRank = 2 →
    N.StructurallyBoundedPositiveTrajectories → N.StructurallyPersistentStd
```

so its three inputs are now:

| input | available to the hole? | source |
|---|---|---|
| `N.WeaklyReversible` | **YES, free** | `weaklyReversible_of_positive_complexBalanced κ hxs hcb`, `:39-45` |
| `N.stoichRank = 2` | only if `hrank` is refined; `hrank : N.stoichRank ≠ 1` gives rank ≥ 2 | `HighCodimensionSiphonFace.lean:133` |
| `N.StructurallyBoundedPositiveTrajectories` | **NOT free** — quantifies over all `κ` and all positive `x₀` (`:46-48`); the hole has `hK`/`hmaps` for one `κ` and one `x₀` | `:46-48`, hole `:118` |

Two consequences, and they point in *opposite* directions:

1. **The boundedness upgrade is now the only obstacle** in this route. `hK : IsCompact K` +
   `hmaps` give boundedness for the given trajectory; the claim needs it for every `κ` and every
   positive `x₀`. Whether that upgrade is derivable is a real question — `Network.genuineOrbit_pos`
   and the `hK`/`hmaps` compactness argument at `GenuineConfinement.lean:63-76` (cited by DEAD-ENDS
   A-68 as already run for the box hypothesis) are the natural starting points, and A-68 records
   that "the box hypothesis is not an extra input".
2. **`StructurallyPersistentStd` is universal, so this route closes the hole by REFUTING its
   hypotheses, not by proving its goal.** Under `hwmax`/`hzeroMax`/`hPmaxne` we have
   `¬ wmax.Positive`, while `StructurallyPersistentStd` asserts every ω-point is positive. Feeding
   the hole's ω-limit hypotheses into that theorem yields `False` — i.e. the hole's twenty
   hypotheses would be **inconsistent**, exactly the ℓ=1 situation of DEAD-ENDS A-57/A-63.

Point 2 is the important structural finding, and it is a *refutation* of the conjunction, not a
proof of the goal. It would be a legitimate way to discharge the `sorry` **only if** the boundedness
upgrade genuinely holds — because `exfalso` is already in scope at the `sorry` (`False` is the goal).
So this is not a dead end: it is a *second, independent* route to `False` that bypasses the blueprint
ladder entirely, and it is now the cheapest untried one.

**Caveat, stated plainly:** I have NOT proved the boundedness upgrade. `StructurallyBoundedPositiveTrajectories`
is deliberately *stronger* than what the hole carries (the module docstring of
`KnownGlobalPersistenceClasses.lean` is explicit that "the compact set may depend on the initial
condition; this captures exactly the trajectory-boundedness hypothesis needed … without silently
strengthening it to permanence"). Whether `∀ κ ∀ x₀` follows is open and is the first thing to
attack. If it does not, this route dies where A-18/A-19 killed `PersistentFrom` — by making a
universal claim that the hole's data cannot support.

## 8. The Pantea route is blocked, and now provably so

§7 left the boundedness upgrade open. It is not: the upgrade has **no producer anywhere in the
tree**.

```
grep -rn "StructurallyBoundedPositiveTrajectories\|PositiveTrajectoriesBoundedForRates" \
     CRNT/ --include=*.lean | grep -v KnownGlobalPersistenceClasses
→ (no output)
```

Definitions, for the record:

- `PositiveTrajectoriesBoundedForRates` — `KnownGlobalPersistenceClasses.lean:40`
- `PositiveTrajectoriesBoundedForFlow` — `:36`, whose docstring is explicit: *"The compact set may
  depend on the initial condition; this captures exactly the trajectory-boundedness hypothesis
  needed by the two-dimensional persistence theorem **without silently strengthening it to
  permanence**."*
- `StructurallyBoundedPositiveTrajectories` — `:46`, `∀ κ, PositiveTrajectoriesBoundedForRates κ`,
  i.e. **all** rate vectors
- `StructurallyPersistentStd` — `CRNT/Dynamics/GlobalPersistence.lean:62`

So the three-input requirement of `TwoDimensionalWRBoundedPersistenceClaim` reduces to:

| input | status |
|---|---|
| `N.WeaklyReversible` | **available free** (`:39-45`, positive CB ⇒ WR) |
| `N.stoichRank = 2` | needs an `hrank` refinement; rank ≥ 2 only |
| `N.StructurallyBoundedPositiveTrajectories` | **no producer; quantified over all `κ` and all positive `x₀`, the hole has one of each** |

The third is not a missing *lemma*; it is a genuinely stronger statement than the hole's data. This
is structurally the same failure as A-18/A-19's `PersistentFrom`: a universal certificate that the
single-trajectory hypotheses cannot support. **Route closed, with evidence, not with a guess.**

Note the asymmetry worth recording: §7's correction (CB ⇒ WR, free) was correct and *necessary* — it
is why the route is not dead on weak reversibility — but the obstacle is the boundedness clause, and
that one is fatal. Both facts are now machine-checked rather than inferred.
