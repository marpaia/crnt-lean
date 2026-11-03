# Statement-drift audit — chain A: `CRNT/Dynamics/HighCodimensionSiphonFace.lean`

26 theorems checked. Line numbers are the 1-based line of the `theorem` keyword, verified against
the file. The module's single `sorry` (line 135) is the known hole and is **not** reported as drift,
but its docstring is audited like any other.

Module-level context read for the vacuity trace: `Siphon.lean:84` (`IsCriticalSiphon`),
`SiphonDimensionDescent.lean:61` (`SiphonCarried`), `:368`
(`comparableGrowthDescent_iff_omegaPointPositive`), `PSemiflow.lean`, `CompatibilityClass.lean:25`
(`StoichCompatible`), `SingleLinkageGAC.lean:46` (`PersistentFrom`), `EndotacticPermanence.lean:58`
(`Permanent`), `FaceCodimension.lean` (`highCodimension_of_not_facet`, `projOn`),
`GACOmegaPositive.lean:133` (`exists_maximal_zeroSet_omegaPoint`), `Lyapunov.lean:58` (`relEntropy`),
and the sole call site `GlobalAttractorTheorem.lean:1555`.

| # | name | file:line | verdict | docstring claim | statement shape | why |
|---|---|---|---|---|---|---|
| 1 | `exists_positive_omegaPoint_of_highCodimension_siphonFace` | 111 | MATCH (hole) | "All hypotheses are exactly the data available at the corresponding point of `complexBalanced_genuinePermanent`" | 20 hyps ⇒ `∃ p ∈ ω, p.Positive` | Conclusion byte-identical to `PositiveOmegaPointForRates`. `hcard`/`hrank` are consequences of `hcodim` (lines 1053, 1090) though the docstring presents them as inputs. |
| 2 | `hsep_fails_of_boundaryPoint_mem_sublevel` | 184 | MATCH | "the separation clause `hsep` is refutable as soon as a boundary point of the ω-limit set sits in the closed sublevel together with the start point" | positive `x₀`, nonneg `wmax`, compat, `wmax s = 0`, both endpoints in sublevel ⇒ `¬ ∃ ε > 0, … ε ≤ x s` | Negates exactly the packaged `hsep`. Non-vacuous: `z = x₀/(n+2) + (1−1/(n+2))·wmax` is genuinely positive and compatible. |
| 3 | `barrier_le_of_mem_omegaLimit` | 272 | MATCH | "Trapping along the orbit puts every ω-limit point into the closed sublevel" | trap on orbit + `w ∈ ω` ⇒ `barrier … ≤ R` | Closure-of-image argument. No extra hypotheses. |
| 4 | `not_persistentFrom_of_mem_omegaLimit_notPositive` | 407 | MATCH | "if the ω-limit set contains a point that is not strictly positive … then `PersistentFrom κ x₀` is refutable" | orbit hyps + `w ∈ ω` + `¬ w.Positive` ⇒ `¬ N.PersistentFrom κ x₀` | The quantified `K₀` is a genuine witness type, not an empty one. |
| 5 | `exists_smaller_carried_siphon_of_zeroSet_inside` | 470 | MATCH | "ω contains no positive point, and some `z ∈ ω` is positive off `Pmax`, vanishes at some species of `Pmax`, positive at some species of `Pmax`" | those ⇒ `∃ Q, Q.Nonempty ∧ IsCriticalSiphon Q ∧ Q.card < Pmax.card ∧ SiphonCarried` | "vanishes at some species of `Pmax`" correctly presented as derived. Witness set non-empty since `hzon` forces `Pmax ≠ ∅`. |
| 6 | `exists_positive_on_pmax_of_zero_outside` | 549 | MATCH | "An ω-point vanishing outside `Pmax` is positive somewhere on `Pmax`" | nonneg + `hmaxExact` + `z ∈ ω` + `∃ t ∉ Pmax, z t = 0` ⇒ `∃ s ∈ Pmax, 0 < z s` | Exactly the claim, non-derivably. |
| 7 | `eq_zero_on_pmax_of_conservation_eq` | 569 | **OVERSTATED** | "a nonnegative `c` positive there forces `z = 0` on `Pmax`. **Then `hmaxExact` collapses `z` to `Pmax` exactly.**" | compat pair + `hout` + `hcnn`/`hcpos` ⇒ `∀ s ∈ Pmax, z s = 0` | The second sentence is not in the statement and does not follow — `hmaxExact` is absent from the hypotheses. |
| 8 | `smaller_carried_siphon_iff_zeroSet_card_lt` | 608 | MATCH | "exists if and only if some ω-point has a strictly smaller zero set than `Pmax`" | `∃ Q … SiphonCarried` ↔ `∃ z ∈ ω, card(Z(z)) < Pmax.card` | Genuine `↔`, both directions proved. `hnoG` disclosed in the surrounding prose. |
| 9 | `omegaPoint_zeroSet_trichotomy` | 658 | **OVERSTATED** | "`hmaxExact` and `hzcard` split *every* ω-point into exactly one of four shapes" | 3-way global disjunction, plain `∨` | Over-claims twice: shapes 1 and 3 are existentially quantified over ω, and "exactly one" asserts exclusivity the `∨` does not provide. The honest reading is in the adjacent prose at 653-654. |
| 10 | `massActionVectorField_eq_zero_on_omegaLimit_of_hypotheses` | 742 | MATCH | "under *exactly* the orbit hypotheses of this module … `massActionVectorField κ z = 0` for *every* `z ∈ omegaLimit` — boundary points included" | orbit hyps + `hxs`/`hcb` ⇒ `∀ z ∈ ω, massActionVectorField κ z = 0` | Delivers the universal claim. Needs *fewer* hypotheses than claimed (`hωaff` unused) — a strengthening, the safe direction. |
| 11 | `uniformLowerBound_offFace_of_zeroSet_eq` | 816 | **DRIFT** | "If every ω-point vanishes on `Pmax`, `hmaxExact` holds, and `t₀ ∉ Pmax`, then there is `ε > 0` with `ε ≤ γ x₀ t t₀` for every `t ≥ 0`" | the same three **plus** `hΓcont : ContinuousOn (γ x₀) (Ici 0)` **plus** `hΓpos : ∀ t ≥ 0, (γ x₀ t).Positive` | Two undisclosed extra hypotheses. `hΓpos` is substantive — orbit positivity is exactly what fails near the face, and the module elsewhere argues it should be *derived*. |
| 12 | `relEntropy_ge_sum_zeroSet` | 931 | MATCH | "the sum of the reference values `xstar s` over `s ∈ Z` is at most `relEntropy xstar x`" | `hxs`, `x.Nonnegative`, `∀ s ∈ Z, x s = 0` ⇒ `∑ s ∈ Z, xstar s ≤ relEntropy xstar x` | Exact match; non-vacuous, and consistent with the module's honest note that it yields no contradiction. |
| 13 | `relEntropy_le_of_mem_omegaLimit` | 957 | MATCH | "Every ω-point … satisfies `relEntropy xstar z ≤ relEntropy xstar x₀`" | those hyps + `z ∈ ω` ⇒ the inequality | Needs no `hK`/`hmaps` — strictly stronger than claimed. Fine. |
| 14 | `sum_xstar_le_relEntropy_x₀_of_zero_omegaPoint` | 996 | MATCH | "If an ω-point `wmax` vanishes exactly on `Pmax`, then `∑ s ∈ Pmax, xstar s ≤ relEntropy xstar x₀`" | `hwmax`, `hwnn`, `hzeroMax` ⇒ the inequality | Exactly the claim. Docstring says "bounded genuine orbit"; the statement needs no boundedness — again a strengthening. |
| 15 | `hmaxExact_of_zeroSet_card_le` | 1034 | MATCH | "`hmaxExact` is derivable from `hzcard` … its zero set contains `Pmax` and is no larger, so the two coincide" | `hzcard`, `z ∈ Ω`, `∀ s ∈ Pmax, z s = 0` ⇒ `∀ s, z s = 0 ↔ s ∈ Pmax` | Pure `Finset.eq_of_subset_of_card_le`. |
| 16 | `two_le_card_of_two_le_finrank_map_projOn` | 1053 | MATCH | "dimension two needs at least two species" | `U : Submodule ℝ (S → ℝ)`, `2 ≤ finrank ℝ (U.map (projOn W))` ⇒ `2 ≤ W.card` | Generalised to arbitrary `U` — a strengthening, correctly scoped by the binder. Empty- and singleton-`W` discharged explicitly. |
| 17 | `stoichRank_ne_one_of_two_le_finrank_map_projOn` | 1090 | MATCH | "a projected rank of at least two forces `stoichRank ≥ 2 ≠ 1`" | the projected-rank hypothesis ⇒ `N.stoichRank ≠ 1` | Exact match. Makes the hole's `hrank` redundant, as the module says at 1080-1084. |
| 18 | `hface_iff_zeroSet_eq` | 1117 | MATCH | "`hface` holds exactly when every ω-point's zero set is `Pmax`" | `(∀ z ∈ Ω, ∀ s ∈ Pmax, z s = 0) ↔ (∀ z ∈ Ω, filter (·=0) = Pmax)` | Genuine `↔`. The `/-!` block at 1104-1112 correctly flags that the *universal* `hface` is unavailable in the tie branch. |
| 19 | `omegaLimit_eq_iInter_closure_tail` | 1143 | MATCH | "the ω-limit set of a single point is the intersection of the closures of the forward tails" | `omegaLimit atTop ϕ {x₀} = ⋂ T, closure (image2 ϕ {t | T ≤ t} {x₀})` | The claim at full generality. |
| 20 | `not_disjoint_closed_cover_omegaLimit` | 1166 | MATCH | "cannot be covered by two disjoint nonempty closed sets" | continuous + precompact + closed disjoint nonempty `A T` covering ω ⇒ `False` | `False` is exactly the claim; `hcont`/precompactness disclosed. |
| 21 | `hface_of_trichotomyThird` | 1343 | MATCH | "then in fact *every* ω-point vanishes on `Pmax`" | those hyps + `hthird` ⇒ `∀ z ∈ ω, ∀ s ∈ Pmax, z s = 0` | `hmaxExact` genuinely used, not decorative. Combined with #9 this kills trichotomy branch 4. |
| 22 | `orbit_stays_in_upperRegion` | 1508 | MATCH | "a continuous orbit which starts in `Zupper`, stays in `Zupper` for all forward time" | `ContinuousOn γ (Ici 0)`, disjoint open cover, `γ 0 ∈ Zupper` ⇒ `∀ t ≥ 0, γ t ∈ Zupper` | Exact match; `isConnected_Ici.image` + `isPreconnected.subset_or_subset` delivers precisely the stated dichotomy. |
| 23 | `persistentFrom_of_upperRegion` | 1538 | MATCH | "the paper's own object — `N.PersistentFrom κ x₀` … is constructed outright, with `K = closure Zupper ∩ {…}`" | region-level `hsplit`, `hε > 0`, `hfloor` ⇒ `N.PersistentFrom κ x₀` | Delivers `PersistentFrom` as defined at `SingleLinkageGAC.lean:46`. The floor genuinely survives `closure Zupper` (the positivity set is closed). **Note: see `UpperRegionAdjudication.lean` — this theorem's hypotheses are jointly unsatisfiable with a boundary ω-point.** |
| 24 | `exists_positive_omegaPoint_of_upperRegion` | 1596 | MATCH | "a floored, never-crossed upper region closes the goal" | orbit-level `hsplit`, `hε > 0`, `hfloor` ⇒ `∃ p ∈ ω, p.Positive` | Conclusion byte-identical to the hole's. **Note: machine-checked dead for hole A — `CRNT.UpperRegionAdjudication.upperRegion_criterion_inconsistent_with_boundaryOmegaPoint`.** |
| 25 | `exists_omegaPoint_vanishing_on_both_sides` | 1692 | MATCH | "some single ω-point vanishes at a member of `I` *and* at a member of `J`" | `hnoG` + `I ∪ J = univ` + `hI` + `hJ` ⇒ `∃ z ∈ ω, ∃ s ∈ I, ∃ t ∈ J, z s = 0 ∧ z t = 0` | The "cannot fire" framing in the section header is about *applying* #20, and is consistent. |
| 26 | `exists_omegaPoint_vanishing_across_siphon` | 1789 | MATCH | "a carried siphon `P` whose complement still holds an ω-point zero is straddled" | `hnoG`, `hPne`, `hcarr`, `hout` ⇒ `∃ z ∈ ω, ∃ s ∈ P, ∃ t ∉ P, z s = 0 ∧ z t = 0` | The `I = P`, `J = Pᶜ` specialisation, exactly as documented. |

## Findings, ranked

1. **OVERSTATED — "Trust status", lines 73-76.** "No other declaration in the tree does [report
   `sorryAx`]" is **false**: `TrueChemistrySRCriterion.lean:8607` is a second site. *Corrected in
   place on this branch; see `research/AUDIT.md` §1.3.*
2. **OVERSTATED — prose at 793-798.** "…**so the trajectory converges to the relative interior of
   the `Pmax` face and all of its limit points are positive exactly on `Pmaxᶜ`**." Neither convergence
   nor that characterisation is proved or stated anywhere; the clause after "so" is an inference the
   file does not discharge.
2b. **OVERSTATED — prose at 1505-1507, now struck.** The paragraph introducing the three Step-4
   lemmas claimed the packaged criteria's refutable clauses "do not touch this shape — **a
   non-convex upper region is exactly what escapes the segment argument**." **Refuted by
   compilation:** `CRNT.UpperRegionAdjudication.upperRegion_criterion_inconsistent_with_boundaryOmegaPoint`.
   `hfloor` is consumed by `closure_minimal` as a fact about `closure Zupper`, and ω-points lie in
   `closure (image2 ϕ v {x₀}) ⊆ closure Zupper`, so convexity is irrelevant. This one sentence is
   what split two rounds of the swarm between opposite verdicts on the fork. **Corrected in place on
   this branch; see `research/AUDIT.md` §4.**
3. **DRIFT — `uniformLowerBound_offFace_of_zeroSet_eq` (816).** Three hypotheses claimed, five
   present. `hΓpos` is the substantive addition (see table).
4. **OVERSTATED — `omegaPoint_zeroSet_trichotomy` (658).** See table; the docstring should adopt the
   weaker reading already given at 653-654.
5. **OVERSTATED — `eq_zero_on_pmax_of_conservation_eq` (569).** See table.
6. **MINOR / stale-doc — hole docstring (96-99).** `hcard`, `hrank` presented as inputs; lines 1053,
   1090 derive them from `hcodim`.
7. **MINOR — line 653 ("Disjuncts 2 and 4 are the open residue").** Superseded within the same file
   by `hface_of_trichotomyThird` (1343). Disclosed later at 1330-1336, so narrative lag, not a false
   statement in isolation.

## No vacuous `Prop` was found

Traced `IsCriticalSiphon` (a conjunction with a genuine `¬ ∃ v ≥ 0` obstruction clause),
`SiphonCarried` (witnessed by an actual ω-point), `PersistentFrom` (witnessed by a compact `K₀`),
`Permanent`, and the `Finset` zero-set filters. In every case the quantified witness sets can be
non-empty.

## The load-bearing chain threads every claimed hypothesis

`highCodimension_of_not_facet` → hole → `complexBalanced_genuinePermanent`, checked line by line at
`GlobalAttractorTheorem.lean:1501-1557`. The six orbit premises arrive as the certificate's own
premises (`hK`/`hmaps` are split from `⟨K, hK, hmaps⟩`); `hwmax`/`hzeroMax`/`hmaxExact`/`hzcard`/
`hPmaxne` come from `exists_maximal_zeroSet_omegaPoint` word-for-word; `hcodim`/`hcard` are the two
components of `highCodimension_of_not_facet`; `hrank` is the `by_cases` else-branch. **No hypothesis
is dropped, strengthened, or weakened.** The residual is genuinely exactly the codimension-≥2 case.

## Why no static argument can close hole A

`CRNT/Examples/CodimTwoFaceModel.lean` exhibits `x₀ = (1,1,1)`, `wmax = (3,0,0)`, `Pmax = {B,C}` on
a catalytic chain, where **every static hypothesis of the hole holds simultaneously and the
conclusion fails**. Any successful proof must use `hsol` — the genuine mass-action differential
equation — essentially.
