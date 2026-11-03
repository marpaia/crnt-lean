# The `analyze` JSON contract

The `analyze` executable computes a network's structural invariants from data, at native speed, with
no per-network elaboration. It is the bulk-scoring counterpart to the codegen certificate workflow
([`generated-certificates.md`](generated-certificates.md)): where codegen emits a kernel-checked Lean
file per network, `analyze` reads a network as JSON and returns its invariants as JSON. The contract
is owned here and versioned, so external consumers depend on a stable shape rather than internal
symbol names.

## Trust boundary

`analyze` uses **compiled evaluation** (compiler trust), so it sits outside the kernel-checked
guarantees of the `CRNT` library. Each reported field is a computable companion of the library theory, and the
derived fields each have a bridge in `CRNT/Interop/Analysis.lean` relating the reported value to its
propositional definition: `analyze_deficiency_eq`, `analyze_stoichRank_eq`,
`analyze_numLinkageClasses_eq`, `analyze_conservationLawDim_eq`, `analyze_weaklyReversible_eq`,
`analyze_acrSpecies_eq`, `analyze_hasSiphon_eq`, `mem_analyze_minimalSiphons`,
`analyze_srSignConsistent_eq`, `analyze_srPMatrixPointIndep_eq`, `analyze_hasCriticalSiphon_eq`,
`analyze_persistenceStructural_eq`, `analyze_noPositivePeriodicOrbitCertified_eq`,
`analyze_stoichRankTwo_eq`, `analyze_persistenceSingleLinkage_eq`,
`analyze_deficiencyOneConditions_eq`, `analyze_numTerminalSLC_eq`, and
`analyze_numDiagonalDriveSpecies_eq`. The point-free P-matrix bridge
`isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep` is proved there too, as is
`analyze_numDiagonalDriveSpecies_eq_card_iff` (the diagonal-drive count reaches `numSpecies` exactly
when `ConsistentDiagonalDrive` holds). The one-sided exclusion
`analyze_hasNoCriticalSiphon_of_hasSiphon_false`, the structural-persistence bridge
`hasNoCriticalSiphon_of_persistenceStructural`, and the certified-persistence verdict
`gac_of_persistenceCertified` (with its precondition lemma `certifiedHypotheses_of_persistenceCertified`)
are proved there too. The oscillation bridge `neverPositivePeriodic_of_analyze` turns a reported
`noPositivePeriodicOrbitCertified = true` into the kernel theorem `NeverPositivePeriodic`; the
`stoichRankTwo` bridge is only a rank-two route selector. Also proved there are the single-linkage precondition bridge
`singleLinkageHypotheses_of_persistenceSingleLinkage` and the deficiency-one bridge
`deficiencyOneConditions_of_analyze`. The margin fields are the reported values of their `…Q` companions, characterized
in the modules that define them (`GershgorinMarginQ`, `GershgorinColumnMarginQ`, `HopfBoundaryQ`), with
`analyze` pinning the inapplicable cases (`analyze_hopfBoundaryMargin_eq_none_of_ne_three`,
`analyze_gershgorinStabilityMargin_eq_none_of_zero_species`,
`analyze_gershgorinColStabilityMargin_eq_none_of_zero_species`); the count fields
`numMinimalSiphons`, `minSiphonSize`, and `numACRSpecies` are sizes/folds of the already-bridged
`minimalSiphons` and `acrSpecies` arrays. When a result needs a kernel-checked certificate for a
specific network, use the codegen contract instead.

## Input: `NetworkData`

A network as a species count and a list of reactions, each a pair of nonnegative integer coefficient
vectors indexed by species position. A coefficient vector shorter than `numSpecies` is zero-padded; a
longer one is truncated — reconstruction (to `Network (Fin numSpecies)`) is total.

```json
{
  "numSpecies": 2,
  "reactions": [
    {"source": [1, 0], "target": [0, 1]},
    {"source": [0, 1], "target": [1, 0]}
  ]
}
```

The input may also be a JSON **array** of such objects, in which case the output is the array of
their analyses (the bulk path: one process invocation scores many networks).

## Output: `Analysis`

`analyze` writes the record with `Json.compress`, which sorts the object keys alphabetically:

```json
{"acrSpecies":[],"conservationLawDim":1,"deficiency":0,"deficiencyOneConditions":true,
 "gershgorinColStabilityMargin":[0,1],"gershgorinStabilityMargin":[0,1],"hasCriticalSiphon":false,
 "hasSiphon":true,"hopfBoundaryMargin":null,"minSiphonSize":2,"minimalSiphons":[[0,1]],
 "noPositivePeriodicOrbitCertified":true,"numACRSpecies":0,"numComplexes":2,
 "numDiagonalDriveSpecies":0,"numLinkageClasses":1,"numMinimalSiphons":1,"numReactions":2,
 "numSpecies":2,"numStrongLinkageClasses":1,"numTerminalSLC":1,"persistenceCertified":true,
 "persistenceSingleLinkage":true,"persistenceStructural":true,"srPMatrixPointIndep":false,
 "srSignConsistent":false,"stoichRank":1,"stoichRankTwo":false,"version":19,"weaklyReversible":true}
```

The fields, in their declaration order on the `Analysis` structure:

| Field | Type | Meaning | Companion |
|---|---|---|---|
| `version` | int | contract version (`analysisVersion`) | — |
| `numSpecies` | int | species count (the `Fin n` carrier size) | — |
| `numComplexes` | int | distinct complexes `n` | `numComplexes` |
| `numReactions` | int | reaction channels | `numReactions` |
| `numLinkageClasses` | int | linkage classes `ℓ` | `computeNumLinkageClasses` |
| `numStrongLinkageClasses` | int | strong linkage classes | `numStrongLinkageClasses` |
| `stoichRank` | int | stoichiometric rank `s` | `computeRank stoichMatrixQ` |
| `conservationLawDim` | int | conservation laws `numSpecies − s` (cokernel dim) | `finrank (orthSum stoichSubspace)` |
| `deficiency` | int | `δ = n − ℓ − s` | `computableDeficiency` |
| `weaklyReversible` | bool | weak reversibility | `decide WeaklyReversible` |
| `acrSpecies` | int[] | species with a structural Shinar–Feinberg ACR witness | `acrSpecies` (`HasShinarFeinbergPair`) |
| `hasSiphon` | bool | a nonempty siphon exists | `IsSiphon` (powerset search) |
| `minimalSiphons` | int[][] | support-minimal siphons, each an ascending index array | `IsMinimalSiphon` |
| `srSignConsistent` | bool | consistent signed species–reaction cover condition holds | `decide ConsistentSRSign` |
| `srPMatrixPointIndep` | bool | point-free full-Jacobian P-matrix precondition: `ConsistentSRSign ∧ ConsistentDiagonalDrive` | `isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep` |
| `hasCriticalSiphon` | bool | a critical siphon exists (no positive conservation law on its support) | `decide HasCriticalSiphon` |
| `persistenceStructural` | bool | structural persistence precondition: `weaklyReversible ∧ ¬hasCriticalSiphon` | `hasNoCriticalSiphon_of_persistenceStructural` |
| `persistenceCertified` | bool | certified persistence: `weaklyReversible ∧ deficiency = 0 ∧ ¬hasCriticalSiphon` | `gac_of_persistenceCertified` |
| `noPositivePeriodicOrbitCertified` | bool | global all-parameter exclusion of nonconstant positive periodic mass-action orbits from `(weaklyReversible ∧ deficiency = 0) ∨ stoichRank ≤ 1` | `neverPositivePeriodic_of_analyze` |
| `stoichRankTwo` | bool | stoichiometric rank is exactly 2; route selector for planar global-dynamics certificates, **not** an oscillation verdict | `analyze_stoichRankTwo_eq` |
| `persistenceSingleLinkage` | bool | single-linkage-class persistence precondition: `weaklyReversible ∧ numLinkageClasses = 1` | `singleLinkageHypotheses_of_persistenceSingleLinkage` |
| `deficiencyOneConditions` | bool | Feinberg deficiency-one conditions (i)+(ii): each linkage class has deficiency ≤ 1 and the per-class deficiencies sum to the network deficiency | `deficiencyOneConditions_of_analyze` |
| `numMinimalSiphons` | int | count of support-minimal siphons | `minimalSiphons.size` |
| `minSiphonSize` | int | smallest minimal-siphon cardinality (`numSpecies + 1` sentinel when none) | derived from `minimalSiphons` |
| `numACRSpecies` | int | count of species with a structural ACR witness | `acrSpecies.size` |
| `numTerminalSLC` | int | terminal strong linkage classes `t` | `computeNumTerminalSLC` |
| `numDiagonalDriveSpecies` | int | species with a positive diagonal drive (`= numSpecies` iff `ConsistentDiagonalDrive`) | `numDiagonalDriveSpecies` |
| `hopfBoundaryMargin` | `[int,int]` or null | `3×3` Routh–Hurwitz Hopf-boundary value `det − trace·c₂` as a `[num, den]` rational; `null` unless `numSpecies = 3` | `hopfBoundaryMarginQ` |
| `gershgorinStabilityMargin` | `[int,int]` or null | row Gershgorin spectral margin `max_k (J k k + ∑_{j≠k} \|J k j\|)` as `[num, den]`; `null` only with no species | `gershgorinStabilityMarginQ` |
| `gershgorinColStabilityMargin` | `[int,int]` or null | column Gershgorin spectral margin `max_k (J k k + ∑_{i≠k} \|J i k\|)` as `[num, den]`; `null` only with no species | `gershgorinColStabilityMarginQ` |

`Analysis` derives `FromJson, ToJson, Repr, DecidableEq`; the `ToJson` instance is what serializes the
record. A rational margin field serializes as a two-element `[numerator, denominator]` array (an
`Int × Int` tuple), and an inapplicable margin as JSON `null`.

`acrSpecies` reports the decidable structural fragment of Shinar–Feinberg ACR (two non-terminal
complexes in distinct linkage classes differing in exactly one species). The deficiency-one side
condition is not a finite decision and is asserted by the consuming objective, not by `analyze`.

`hasSiphon` enumerates the species powerset (`2^numSpecies`, fine for small networks) and reports
whether any nonempty siphon exists. It is one-sided: `false` soundly excludes any *critical* siphon
(`analyze_hasNoCriticalSiphon_of_hasSiphon_false`), hence — with weak reversibility and complex
balancing — persistence; `true` is inconclusive. The exclusion is narrow in practice: for a closed
network the full species set is always a siphon, so `hasSiphon = false` arises only with a synthesis
reaction (`0 → y`).

`hasCriticalSiphon` is `decide HasCriticalSiphon`: the full critical-siphon verdict. A siphon is
critical iff it carries no positive conservation law on its exact support; `hasCriticalSiphon` reports
whether any nonempty siphon is critical. Each candidate's criticality reduces to a rational linear
feasibility problem (sign-restricted conservation-cone membership), decided by Fourier–Motzkin
elimination — the constructive content of Farkas' lemma. A species enumeration is drawn computably
from the `Fintype` and the decision lifted through the subsingleton of `Decidable`, so the verdict is
computable. It is two-sided: `false` soundly establishes the absence of a critical siphon, hence —
with weak reversibility and complex balancing — persistence.

`persistenceStructural` is `weaklyReversible ∧ ¬hasCriticalSiphon`: the decidable *structural*
precondition of the global-attractor persistence verdict. When `true` it certifies exactly
`WeaklyReversible ∧ HasNoCriticalSiphon` (`hasNoCriticalSiphon_of_persistenceStructural`), the
structural half of the hypothesis of `gac_of_hasNoCriticalSiphon` (the decision-driven form
`gac_of_decide` discharges the criticality exclusion from `decide`). It is **not** a full persistence
proof: the global-attraction conclusion additionally needs a positive complex-balanced reference,
which the consumer supplies and the contract cannot certify from structure alone.

`persistenceCertified` is `weaklyReversible ∧ deficiency = 0 ∧ ¬hasCriticalSiphon`: the full
structural precondition under which the contract supplies the complex-balanced reference itself. When
`true` the network is weakly reversible, of deficiency zero, and has no critical siphon
(`certifiedHypotheses_of_persistenceCertified`), so the Feinberg–Horn–Jackson deficiency-zero theorem
produces the positive complex-balanced equilibrium that `persistenceStructural` left to the consumer.
The verdict `gac_of_persistenceCertified` then concludes, for any positive rate constants and any
positive start `x₀`, that the mass-action semiflow through `x₀` converges to a complex-balanced
equilibrium in `x₀`'s own compatibility class (its ω-limit set is exactly that point). The only input
the contract cannot certify is the positive start `x₀`, a per-trajectory hypothesis rather than a
structural one. In words: every positive trajectory converges to the network's complex-balanced
equilibrium in its compatibility class. Deficiency zero is read off `deficiency` and bridged to
`DeficiencyZero` by `deficiencyZero_iff_computableDeficiency_eq_zero`.

`noPositivePeriodicOrbitCertified` is `(weaklyReversible ∧ deficiency = 0) ∨ stoichRank ≤ 1`.  When true,
`neverPositivePeriodic_of_analyze` proves the reconstructed network is `NeverPositivePeriodic`: for
every positive mass-action rate vector, every positive periodic solution is constant.  This is a
global theorem, not a Jacobian-at-one-point stability test.  `stoichRankTwo` is deliberately weaker:
it only reports `stoichRank = 2`, identifying compatibility classes where planar
Poincare--Bendixson/Bendixson--Dulac certificates may later apply.  It is not evidence for or against
oscillation by itself.

`persistenceSingleLinkage` is `weaklyReversible ∧ numLinkageClasses = 1`: the decidable structural
precondition of the *other* persistence mechanism, Anderson's single-linkage-class global attractor,
rather than the no-critical-siphon route behind `persistenceStructural`. When `true` it discharges the
structural hypotheses of `gac_of_singleLinkage_decide`
(`singleLinkageHypotheses_of_persistenceSingleLinkage`). It is **not** a full persistence proof: it
additionally needs a positive complex-balanced reference and Anderson's single-linkage persistence
implication, which the consumer supplies.

`deficiencyOneConditions` is `decide DeficiencyOneConditions`: conditions (i) and (ii) of Feinberg's
deficiency-one theorem — every linkage class has deficiency at most one, and the per-class deficiencies
sum to the network deficiency. Its per-class deficiencies route through `computeRank`, so this field is
compiled-evaluation only and does **not** reduce under `by decide`. It is **not** a full deficiency-one
verdict: the theorem additionally requires each linkage class to have exactly one terminal strong
linkage class (`deficiencyOneConditions_of_analyze`).

`minimalSiphons` lists the support-minimal siphons (each as an ascending species-index array). These
are the candidate critical siphons: a siphon is critical iff it carries no positive conservation law
on its support. Enumeration tests minimality across the powerset (`~4^numSpecies` in the worst case —
fine for the small networks evaluated here).

`srSignConsistent` is `decide ConsistentSRSign`: the consistent signed species–reaction cover
condition, the decidable sign fragment of the Craciun–Feinberg species–reaction graph injectivity
criterion. Over every restricted species set, every reaction-choice cover carries a nonnegative
signed-incidence weight, read in `ℤ` where the order is decidable. It is **not** a full injectivity
verdict: discharging mass-action injectivity (and monostationarity) on a positive compatibility
class additionally requires the chart-box, positivity, positive-diagonal, and coordinate-selection
hypotheses, which the consumer supplies. When `true`, the network satisfies the verdict's sign
hypothesis (`hweight_of_consistentSRSign`).

`srPMatrixPointIndep` is `decide ConsistentSRSign && decide ConsistentDiagonalDrive`: the two
decidable point-free conditions of the Craciun–Feinberg point-independence keystone — the consistent
signed cover, and a per-species reaction that depends on and increases the species
(`ConsistentDiagonalDrive`, the computable companion of `PositiveDiagonalDrive`). When `true`, the
full mass-action Jacobian is a P-matrix at every positive concentration, for every positive rate
constants, with no per-point hypothesis (`isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep`).
This is the sound point-free face of the injectivity criterion. It is still **not** a full
injectivity verdict: carrying the full-Jacobian P-matrix property to compatibility-class injectivity
needs a coordinate chart whose reduced Jacobian is a P-matrix on a box. The reduced Jacobian of any
such chart is a Schur-style oblique compression of the full Jacobian, not a principal submatrix, so
the full-Jacobian P-matrix property does not transport to it by submatrix selection; the chart-box
reduced-Jacobian P-matrix hypothesis remains a consumer input to
`massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix`, the non-vacuous pivot-chart injectivity
theorem.

The deficiency assembly `δ = n − ℓ − s` is owned by the library (`computableDeficiency`), not the
consumer: `computeNumLinkageClasses` supplies a computable `ℓ` (the quotient `numLinkageClasses` does
not evaluate), and `deficiency_eq_computableDeficiency` bridges the assembly to the propositional
`deficiency`.

## Dense margins and counts

Alongside the boolean and integer invariants, the record carries dense scalar fields: graded companions
of the verdicts, whose value moves continuously and whose sign or threshold coincides with a boolean
flip. They exist so a consumer has a gradient to follow, not only a pass/fail (see *Using the record
downstream*).

`numMinimalSiphons`, `minSiphonSize`, and `numACRSpecies` grade the siphon and ACR fields:
`numMinimalSiphons` is `minimalSiphons.size`; `minSiphonSize` is the smallest support-minimal-siphon
cardinality, with a `numSpecies + 1` sentinel when there is none (a smaller value is a tighter
extinction obstruction, the sentinel marks no obstruction); `numACRSpecies` is `acrSpecies.size`.

`numTerminalSLC` is the terminal-strong-linkage-class count `t` (`analyze_numTerminalSLC_eq`).
`numDiagonalDriveSpecies` counts the species carrying a positive diagonal drive — a reaction that
depends on and increases the species; it equals `numSpecies` exactly when `ConsistentDiagonalDrive`
holds (`analyze_numDiagonalDriveSpecies_eq_card_iff`), so the gap `numSpecies − numDiagonalDriveSpecies`
measures how far the network is from the per-species half of the point-free P-matrix injectivity
precondition. It does not grade the signed-cover half (`srSignConsistent`).

`hopfBoundaryMargin` is the `3 × 3` Routh–Hurwitz Hopf-boundary value `det − trace · c₂` of the
rational mass-action Jacobian at the all-ones concentration with unit rate constants, a
`[numerator, denominator]` rational, and `null` unless `numSpecies = 3`
(`analyze_hopfBoundaryMargin_eq_none_of_ne_three`). It is zero exactly on the cubic Hopf boundary — a
graded proximity-to-oscillation signal at one chart point, not a bifurcation verdict (the limit-cycle
conclusion needs center-manifold theory).

`gershgorinStabilityMargin` is the Gershgorin local-stability spectral margin
`max_k ( J k k + ∑_{j≠k} |J k j| )` of that same Jacobian, a `[numerator, denominator]` rational, and
`null` only when there are no species (`analyze_gershgorinStabilityMargin_eq_none_of_zero_species`). It
is **negative exactly when the row diagonal-dominance test certifies the linearization there is
Hurwitz** (locally stable, no oscillation), in any number of species; the magnitude grades the
stability robustness. It is a one-directional sufficient stability margin, not a full spectral verdict:
a nonnegative value can still belong to a Hurwitz matrix. `gershgorinColStabilityMargin` is the column
companion `max_k ( J k k + ∑_{i≠k} |J i k| )`
(`analyze_gershgorinColStabilityMargin_eq_none_of_zero_species`); the row and column tests are distinct
sufficient conditions, so it is an independent stability certificate.

## Using the record downstream

The record serves two kinds of consumer, and the field types mark the split.

**Boolean verdicts are hard design filters.** Each `Bool` (and the integer invariant it reads) settles
a structural question for *every* positive rate constant at once, so a design tool can rule a candidate
in or out before fitting a single parameter:

- `weaklyReversible = true` together with `deficiency = 0` are the deficiency-zero theorem's
  hypotheses.  The dedicated `noPositivePeriodicOrbitCertified = true` field now also packages the independent rank-at-most-one exclusion route in addition to these
  hypotheses and bridges to the all-parameter theorem excluding nonconstant positive periodic
  mass-action orbits.  Do not infer the same conclusion from `deficiency = 0` alone.
- `persistenceCertified = true` upgrades that to a global no-extinction verdict: for any positive rate
  constants and positive start, every trajectory converges to the network's complex-balanced
  equilibrium in its own compatibility class (`gac_of_persistenceCertified`). `persistenceStructural =
  true` is the same screen but leaves the positive complex-balanced reference for the consumer to
  supply.
- `hasCriticalSiphon = true` flags a species set that can be driven to extinction; `hasSiphon = false`
  or `hasCriticalSiphon = false` rules extinction out — the former is what a kill-switch design wants,
  the latter what a persistent/homeostatic design wants.
- `srPMatrixPointIndep = true` discharges the point-free half of the Craciun–Feinberg injectivity
  criterion (the full mass-action Jacobian is a P-matrix everywhere positive), the structural
  precondition for monostationarity; `acrSpecies` names the species with a structural ACR witness, a
  robust-output (homeostat) target.

Because each boolean is a computable companion tied to its propositional definition by a bridge
theorem, a `true` verdict is a signal the consumer re-derives, not one it trusts.

**Dense margins are graded signals for search and learning.** A boolean gives a sparse pass/fail; a
margin gives a continuous quantity whose sign or threshold flips exactly where the boolean does, so an
optimizer or a reinforcement-learning loop can follow a gradient toward (or away from) a target region
while the signal stays a verified companion rather than a learned proxy. Concretely:

- drive `gershgorinStabilityMargin` (or its column form) *more negative* as a dense "make the
  linearization more robustly stable" objective — it crosses zero into a certified-Hurwitz region, and
  the magnitude reports the margin of safety. A nonnegative value is inconclusive (the test is
  sufficient, not necessary), not evidence of instability. On the worked examples, `0 → A → 0` reports
  `[-1,1] = −1` (certified stable) while the reversible pair `A ⇌ B` reports `[0,1] = 0` (on the
  boundary).
- move `hopfBoundaryMargin` *toward zero* to search for an oscillation onset, or *away from zero* to
  keep a monostable design clear of one (3-species networks).
- treat `minSiphonSize` and the counts (`numMinimalSiphons`, `numACRSpecies`, `numTerminalSLC`,
  `numDiagonalDriveSpecies`) as graded companions of the siphon, ACR, and injectivity fields:
  `numSpecies − numDiagonalDriveSpecies → 0` is a dense path toward `ConsistentDiagonalDrive`, and a
  larger `minSiphonSize` (up to the sentinel) is a weaker extinction obstruction.

All margins come through the compiled `analyze` path, so they carry compiler trust (the trust boundary
above); for a kernel-checked certificate of a specific verdict, use the codegen contract.

## Versioning

`version` is the value of `analysisVersion` (`CRNT/Interop/Analysis.lean`), currently `19`. It tags the
field set and increments whenever a field is added or its meaning changes, so a consumer can detect a
contract it does not understand. A new per-property companion raises the version when it joins the
record. A consumer should read fields by name and treat an absent field as undecided, so a record
produced by a newer contract than it understands degrades gracefully rather than misreads.

## Usage

```shell
echo '{"numSpecies":2,"reactions":[{"source":[1,0],"target":[0,1]},
      {"source":[0,1],"target":[1,0]}]}' | lake exe analyze
```

Invalid input is reported on stderr with a nonzero exit; the trust boundary means a malformed network
never yields a structural verdict.

## Modules

- `CRNT/Interop/NetworkData.lean`: `NetworkData`/`ReactionData`, `FromJson`/`ToJson`, and `toNetwork`.
- `CRNT/Interop/Analysis.lean`: `Analysis`, `analyze`, and the field bridges.
- `CRNT/Decision/ComputableDeficiency.lean`: `computeNumLinkageClasses`, `computableDeficiency`, and
  `deficiency_eq_computableDeficiency`.
- `CRNT/Decision/ACRCheck.lean`: `HasShinarFeinbergPair`, `acrSpecies`, and `mem_acrSpecies`.
- `CRNT/Dynamics/Siphon.lean`: `IsSiphon`, `IsMinimalSiphon`, `minimalSiphons`, `HasNoCriticalSiphon`,
  and the exclusion lemma `hasNoCriticalSiphon_of_forall_not_isSiphon`.
- `CRNT/Multistationarity/SRSignDecidable.lean`: `ConsistentSRSign`, its `Decidable` instance, and
  `hweight_of_consistentSRSign` (the SR-sign injectivity fragment).
- `CRNT/Multistationarity/PointIndepDecidable.lean`: `ConsistentDiagonalDrive` and the point-free
  full-Jacobian P-matrix keystone `isPMatrix_massActionJacobian_box_of_decide`.
- `CRNT/Decision/InjectivityMargin.lean`: `numDiagonalDriveSpecies` and
  `numDiagonalDriveSpecies_eq_card_iff` (the graded diagonal-drive companion).
- `CRNT/Decision/CriticalSiphonDecide.lean`: `HasCriticalSiphon`, its computable `Decidable`
  instance (rational feasibility by Fourier–Motzkin elimination), and `supportedFeasSystem`.
- `CRNT/Decision/PersistenceVerdict.lean`: `gac_of_decide`, the decision-driven global-attractor
  persistence verdict composing the critical-siphon test with `gac_of_hasNoCriticalSiphon`.
- `CRNT/Decision/PersistenceCertified.lean`: `gac_of_deficiencyZero_decide`, the certified-persistence
  verdict that supplies the complex-balanced reference from the deficiency-zero theorem.
- `CRNT/Decision/PersistenceSingleLinkage.lean`: `gac_of_singleLinkage_decide`, the single-linkage-class
  global-attractor verdict, and `singleLinkageClass_of_computeNumLinkageClasses_eq_one`.
- `CRNT/Decision/DeficiencyOneConditionsDecide.lean`: `DeficiencyOneConditions` and its
  `decidableDeficiencyOneConditions` instance (conditions (i) and (ii) of the deficiency-one theorem).
- `CRNT/Decision/ComputableTerminalSLC.lean`: `computeNumTerminalSLC` and its bridge to `numTerminalSLC`.
- `CRNT/Dynamics/HopfBoundaryQ.lean`: `hopfBoundaryMarginQ`, the rational `3×3` Hopf-boundary value.
- `CRNT/Dynamics/GershgorinMarginQ.lean`, `CRNT/Dynamics/GershgorinColumnMarginQ.lean`:
  `gershgorinStabilityMarginQ` / `gershgorinColStabilityMarginQ`, the rational row/column stability
  margins negative exactly when the diagonal-dominance test certifies Hurwitz.
- `CRNT/LinearAlgebra/OrthogonalComplement.lean`: `orthSum` and `finrank_orthSum` (conservation laws).
- `Analyze.lean`: the `lake exe analyze` entry point.

## Related documents

- [`generated-certificates.md`](generated-certificates.md): the per-network kernel-checked codegen
  contract — the provenance path, complementary to this throughput path.
- [`decidability.md`](decidability.md): the decision procedures and computable companions the fields
  rest on.

## Version history

### 19

The union of the three development branches' contracts. Restores the four persistence fields that
v18 removed, now backed by real definitions: `CRNT/Dynamics/SiphonAutocatalysis.lean` defines
`IsDrainable` and `IsSelfReplicable` in terms of reaction pathways and decides them through
`isDrainable_iff_feasible_negativeFluxSystem` and the rational-Farkas layer, so the flags are no
longer constant. Adds the oscillation branch's `noPositivePeriodicOrbitCertified` and
`stoichRankTwo`, with `neverPositivePeriodic_of_analyze` as the proof-producing bridge.

### 18 (superseded)

Removes four fields that were unconditionally `true` for every input network, together with the
three certificate bridges built on them:

* `noDrainableSiphon`
* `noSelfReplicableSiphon`
* `minimalCriticalSiphonDichotomy`
* `persistenceSiphonDichotomy`

Their underlying predicates in `CRNT/Dynamics/SiphonAutocatalysis.lean` were defined as
`∃ (_ : Unit), True` with `Decidable` instances given by `isTrue`, so `decide P = true` held for
every network. Consumers reading these fields were reading a constant, and
`boundaryOmegaCertificate_of_persistenceSiphonDichotomy` produced a `BoundaryOmegaCertificate`
whose only field was `dummy : True`. See `LEDGER.md`.

Adds `gac_of_persistenceCertified`: when `persistenceCertified` is `true`, every positive trajectory
converges to the network's complex-balanced equilibrium in its own compatibility class. This one is
real — it routes through the proved `gac_of_deficiencyZero_decide`.

These fields return when the siphon predicates carry their intended meaning and the certificates
carry the statements they are supposed to witness.

### 17

Added the four fields above. Superseded; do not rely on a `version = 17` report.
