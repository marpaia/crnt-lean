import CRNT.Interop.NetworkData
import CRNT.Decision.ComputableDeficiency
import CRNT.Decision.DirectedReachability
import CRNT.Decision.ACRCheck
import CRNT.Decision.CriticalSiphonDecide
import CRNT.Decision.PersistenceVerdict
import CRNT.Decision.PersistenceCertified
import CRNT.Decision.PersistenceSingleLinkage
import CRNT.Decision.DeficiencyOneConditionsDecide
import CRNT.Dynamics.Siphon
import CRNT.LinearAlgebra.OrthogonalComplement
import CRNT.Multistationarity.SRSignDecidable
import CRNT.Multistationarity.PointIndepDecidable
import CRNT.Decision.ComputableTerminalSLC
import CRNT.Decision.InjectivityMargin
import CRNT.Dynamics.HopfBoundaryQ
import CRNT.Dynamics.GershgorinMarginQ
import CRNT.Dynamics.GershgorinColumnMarginQ
import CRNT.Oscillation.LowRank
import CRNT.Dynamics.GlobalPersistenceCertificates

/-!
# One-call structural analysis

`analyze` maps a `NetworkData` to an `Analysis`: the network's structural invariants in one
computable record, ready to serialize as JSON. It is the stable contract an external evaluator
consumes — every field is a computable companion of the library theory, so a compiled analyzer
produces them at native speed with no per-network elaboration, and the library (not the consumer)
owns the `δ = n − ℓ − s` assembly.

Each numeric field has a bridge back to its propositional definition: `analyze_deficiency_eq`
(`δ`), `analyze_stoichRank_eq` (`s`), `analyze_numLinkageClasses_eq` (`ℓ`), and
`analyze_conservationLawDim_eq` (the dimension of the conservation-law space, `orthSum` of the
stoichiometric subspace). The `weaklyReversible` flag is `decide N.WeaklyReversible`, sound by the
`Decidable` instance. `acrSpecies` lists the species carrying the structural Shinar–Feinberg ACR
witness (`analyze_acrSpecies_eq`), the decidable fragment; the deficiency-one side condition is
supplied by the consumer. `hasSiphon` flags the existence of a nonempty siphon
(`analyze_hasSiphon_eq`); when `false` it soundly excludes any critical siphon
(`analyze_hasNoCriticalSiphon_of_hasSiphon_false`), the Farkas-free persistence design filter.
`minimalSiphons` lists the support-minimal siphons as ascending species-index arrays
(`mem_analyze_minimalSiphons`) — the species sets a consumer's criticality feasibility check tests.
`srSignConsistent` is `decide N.ConsistentSRSign` (`analyze_srSignConsistent_eq`), the decidable
signed species–reaction cover fragment of the Craciun–Feinberg injectivity criterion; it is not a
full injectivity verdict, which additionally needs the consumer's chart-box, positivity, and
positive-diagonal hypotheses. `srPMatrixPointIndep` is
`decide N.ConsistentSRSign && decide N.ConsistentDiagonalDrive`
(`analyze_srPMatrixPointIndep_eq`), the decidable point-free precondition under which the full
mass-action Jacobian is a P-matrix at every positive concentration
(`isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep`) — the point-free keystone of the
Craciun–Feinberg criterion. It is still not a full injectivity verdict: carrying it to
compatibility-class injectivity needs a coordinate chart whose reduced Jacobian is a P-matrix on a
box (an oblique compression that the full-Jacobian P-matrix property does not transport to by
submatrix selection), supplied to `massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix`. `hasCriticalSiphon` is `decide N.HasCriticalSiphon`
(`analyze_hasCriticalSiphon_eq`), the full critical-siphon verdict: a nonempty siphon carrying no
positive conservation law on its exact support, decided by rational feasibility (Fourier–Motzkin
elimination). When `false` the network has no critical siphon, so (weakly reversible and complex
balanced) it is persistent. `persistenceStructural` is `weaklyReversible ∧ ¬hasCriticalSiphon`
(`analyze_persistenceStructural_eq`): the decidable *structural* precondition of the global-attractor
persistence verdict. When `true` it certifies exactly `WeaklyReversible ∧ HasNoCriticalSiphon`
(`hasNoCriticalSiphon_of_persistenceStructural`), the structural half of `gac_of_hasNoCriticalSiphon`'s
hypothesis; it is **not** a full persistence proof — the global-attraction conclusion additionally
needs a positive complex-balanced reference, which the consumer supplies and the contract cannot
certify from structure alone.

`numMinimalSiphons`, `minSiphonSize`, and `numACRSpecies` are dense scalar companions of the siphon
and ACR fields: the count of minimal siphons, the smallest minimal-siphon cardinality (with a
`numSpecies + 1` sentinel when there are none — a smaller value is a tighter extinction obstruction),
and the ACR-species count. `numTerminalSLC` is the terminal-strong-linkage-class count `t`
(`analyze_numTerminalSLC_eq`). `numDiagonalDriveSpecies` counts the positively-driven species; it
equals `numSpecies` exactly when `ConsistentDiagonalDrive` holds
(`analyze_numDiagonalDriveSpecies_eq_card_iff`), the graded per-species half of the point-free
P-matrix injectivity precondition. `hopfBoundaryMargin` is the `3 × 3` Routh–Hurwitz Hopf-boundary
value `det − trace · c₂Fin3` of the rational mass-action Jacobian at the all-ones concentration with
unit rate constants, a `(numerator, denominator)` pair and `none` unless `numSpecies = 3`
(`analyze_hopfBoundaryMargin_eq_none_of_ne_three`); it is a graded proximity-to-oscillation signal at
one chart point, not a bifurcation verdict. `gershgorinStabilityMargin` is the Gershgorin
local-stability spectral margin `max_k ( J k k + ∑_{j≠k} |J k j| )` of the rational mass-action
Jacobian at the all-ones concentration with unit rate constants, a `(numerator, denominator)` pair and
`none` only when there are no species (`analyze_gershgorinStabilityMargin_eq_none_of_zero_species`).
Negative exactly when the row diagonal-dominance test certifies the linearization there is Hurwitz, in
any dimension; the magnitude grades stability robustness. It is a one-directional sufficient stability
margin, not a full spectral verdict. `gershgorinColStabilityMargin` is the column companion
`max_k ( J k k + ∑_{i≠k} |J i k| )` of the same Jacobian
(`analyze_gershgorinColStabilityMargin_eq_none_of_zero_species`); the row and column tests are distinct
sufficient conditions, so it is an independent stability certificate, negative exactly when the column
diagonal-dominance test certifies Hurwitz.

`version` tags the JSON contract; bump it whenever the field set changes.

Depends on: `CRNT.Interop.NetworkData`,
`CRNT.Decision.ComputableDeficiency`, `CRNT.Decision.DirectedReachability`.
-/

namespace CRNT

open Lean (FromJson ToJson)
open CRNT.GaussianRank
open scoped NNReal Topology

/-- The version of the `Analysis` JSON contract. Bump on any field-set change. -/
def analysisVersion : Nat := 19

/-- The structural invariants of a network, as a JSON-serializable record. The numeric fields are
the computable companions of the library theory; `deficiency` is `n − ℓ − s` assembled here. -/
structure Analysis where
  /-- The contract version (`analysisVersion`). -/
  version : Nat
  /-- The number of species. -/
  numSpecies : Nat
  /-- The number of distinct complexes `n`. -/
  numComplexes : Nat
  /-- The number of reaction channels. -/
  numReactions : Nat
  /-- The number of linkage classes `ℓ`. -/
  numLinkageClasses : Nat
  /-- The number of strong linkage classes. -/
  numStrongLinkageClasses : Nat
  /-- The stoichiometric rank `s`. -/
  stoichRank : Nat
  /-- The dimension of the conservation-law space, `numSpecies − stoichRank`: the number of
  independent linear conservation laws (the cokernel of the stoichiometric map). -/
  conservationLawDim : Nat
  /-- The deficiency `δ = n − ℓ − s`. -/
  deficiency : Nat
  /-- Whether the network is weakly reversible. -/
  weaklyReversible : Bool
  /-- The species indices carrying a structural Shinar–Feinberg ACR witness (decidable fragment;
  the deficiency-one side condition is supplied by the consumer). -/
  acrSpecies : Array Nat
  /-- Whether the network has a nonempty siphon. When `false`, the network has no critical siphon,
  so (weakly reversible and complex balanced) it is persistent — a sound design filter. -/
  hasSiphon : Bool
  /-- The support-minimal siphons, each as an ascending array of species indices. These are the
  candidate critical siphons a persistence/extinction analysis tests for feasibility. -/
  minimalSiphons : Array (Array Nat)
  /-- Whether the network satisfies the consistent signed species–reaction cover condition
  (`ConsistentSRSign`): the decidable sign fragment of the Craciun–Feinberg species–reaction graph
  injectivity criterion. When `true`, the network discharges the verdict's sign hypothesis; a full
  injectivity verdict additionally needs the chart-box, positivity, and positive-diagonal
  hypotheses the consumer supplies. -/
  srSignConsistent : Bool
  /-- Whether the network meets the decidable point-free precondition of the full-Jacobian P-matrix
  verdict: the consistent signed species–reaction cover condition together with a per-species
  positively-driving reaction (`ConsistentSRSign ∧ ConsistentDiagonalDrive`). When `true`, the full
  mass-action Jacobian is a P-matrix at every positive concentration, for every positive rate
  constants, read off the signed species–reaction graph alone with no per-point hypothesis. This is
  the point-free keystone of the Craciun–Feinberg injectivity criterion; it is **not** a full
  injectivity verdict — carrying it to compatibility-class injectivity needs a coordinate chart whose
  reduced Jacobian is a P-matrix on a box, a Schur-style oblique compression that the full-Jacobian
  P-matrix property does not transport to by submatrix selection, so the chart-box reduced-Jacobian
  P-matrix hypothesis remains a consumer input. -/
  srPMatrixPointIndep : Bool
  /-- Whether the network has a critical siphon: a nonempty siphon carrying no positive conservation
  law on its exact support. When `false`, the network has no critical siphon, so (weakly reversible
  and complex balanced) it is persistent. The verdict is decided by rational feasibility
  (Fourier–Motzkin elimination), the constructive content of Farkas' lemma. -/
  hasCriticalSiphon : Bool
  /-- Whether the network meets the decidable *structural* precondition of the global-attractor
  persistence verdict: `weaklyReversible ∧ ¬hasCriticalSiphon`. When `true` it certifies
  `WeaklyReversible ∧ HasNoCriticalSiphon` — the structural half of `gac_of_hasNoCriticalSiphon`'s
  hypothesis. It is not a full persistence proof: the global-attraction conclusion additionally needs
  a positive complex-balanced reference the consumer supplies. -/
  persistenceStructural : Bool
  /-- Whether the network meets the full structural precondition of the global-attractor verdict with
  the complex-balanced reference supplied internally: `weaklyReversible ∧ deficiency = 0 ∧
  ¬hasCriticalSiphon`. When `true`, the network is weakly reversible, of deficiency zero, and has no
  critical siphon, so the Feinberg–Horn–Jackson deficiency-zero theorem provides the complex-balanced
  reference and every positive trajectory converges to the complex-balanced equilibrium in its own
  compatibility class. The only remaining input is the positive start — a per-trajectory hypothesis,
  not a structural one. -/
  persistenceCertified : Bool
  /-- Whether the analyzer can certify **structural non-oscillation** for every positive mass-action
  rate vector.  Two independent global routes are currently compiled: (i) weak reversibility plus
  deficiency zero (Horn--Jackson), or (ii) stoichiometric rank at most one (one-dimensional autonomous
  dynamics).  This is an all-parameter exclusion of nonconstant positive periodic orbits, not merely
  local linear stability at one concentration. -/
  noPositivePeriodicOrbitCertified : Bool
  /-- Whether the stoichiometric rank is exactly two.  This is not an oscillation verdict; it marks
  networks whose positive compatibility classes are two-dimensional, the setting where a future
  Poincare--Bendixson/Bendixson--Dulac certificate can give global periodic-orbit conclusions. -/
  stoichRankTwo : Bool
  /-- Whether the network meets the decidable structural precondition of the single-linkage-class
  global-attractor verdict: it is weakly reversible and has a single linkage class
  (`weaklyReversible ∧ computeNumLinkageClasses = 1`). This is the *other* persistence mechanism from
  `persistenceStructural` — Anderson's single-linkage-class global attractor rather than the
  no-critical-siphon route. When `true` it discharges the structural hypotheses of
  `gac_of_singleLinkage_decide`; it is not a full persistence proof, which additionally needs a
  positive complex-balanced reference and Anderson's single-linkage persistence implication. -/
  persistenceSingleLinkage : Bool
  /-- Whether the network has no drainable siphon. This is now an exact decidable pathway-cone
  verdict: strict real fluxes are converted to rational fluxes and then to finite reaction
  multiplicities by `StrictConeRealization`. -/
  noDrainableSiphon : Bool
  /-- Whether the network has no self-replicable siphon (the non-autocatalytic siphon condition).
  This is likewise decided exactly through rational linear feasibility. -/
  noSelfReplicableSiphon : Bool
  /-- Whether every minimal critical siphon in this concrete network is drainable or
  self-replicable. The universal Deshpande--Gopalkrishnan theorem remains a theorem frontier, but
  the proposition for a fixed finite network is decidable and therefore certifiable. -/
  minimalCriticalSiphonDichotomy : Bool
  /-- Proof-producing omega-persistence route based on the verified siphon dichotomy:
  `weaklyReversible ∧ minimalCriticalSiphonDichotomy ∧
  (noDrainableSiphon ∨ noSelfReplicableSiphon)`. A true value yields a
  `BoundaryOmegaCertificate` with no unproved flux-realization premise. -/
  persistenceSiphonDichotomy : Bool
  /-- Whether the network satisfies Feinberg's deficiency-one linkage conditions
  (`DeficiencyOneConditions`): every linkage class has deficiency at most one and the per-class
  deficiencies sum to the network deficiency — conditions (i) and (ii) of the deficiency-one theorem.
  Decided by compiled evaluation (the per-class deficiencies route through `computeRank`), so unlike
  the kernel-reducing flags this field is `#eval`-only and does not reduce under `by decide`. It is
  not a full deficiency-one verdict: the theorem additionally requires each linkage class to have
  exactly one terminal strong linkage class. -/
  deficiencyOneConditions : Bool
  /-- The number of support-minimal siphons (`minimalSiphons.size`). -/
  numMinimalSiphons : Nat
  /-- The minimum cardinality among the support-minimal siphons, or the `numSpecies + 1` sentinel
  when there are none. A smaller value is a tighter structural extinction obstruction; the sentinel
  marks the absence of any minimal siphon (no obstruction). -/
  minSiphonSize : Nat
  /-- The number of species carrying a structural Shinar–Feinberg ACR witness (`acrSpecies.size`). -/
  numACRSpecies : Nat
  /-- The number of terminal strong linkage classes `t`. -/
  numTerminalSLC : Nat
  /-- The number of species carrying a positive diagonal drive: a reaction that depends on and
  increases the species. Equals `numSpecies` exactly when `ConsistentDiagonalDrive` holds — the
  per-species half of the point-free P-matrix injectivity precondition, exposed as a graded
  robustness count. It does not grade the signed-cover half (`srSignConsistent`). -/
  numDiagonalDriveSpecies : Nat
  /-- The `3 × 3` Routh–Hurwitz Hopf-boundary value `det − trace · c₂Fin3` of the rational
  mass-action Jacobian at the all-ones concentration with unit rate constants, as a
  `(numerator, denominator)` pair; `none` unless `numSpecies = 3`. Zero exactly on the cubic Hopf
  boundary — a graded proximity-to-oscillation signal at one chart point, not a bifurcation verdict
  (the limit-cycle conclusion needs center-manifold theory). -/
  hopfBoundaryMargin : Option (Int × Int)
  /-- The Gershgorin local-stability spectral margin `max_k ( J k k + ∑_{j≠k} |J k j| )` of the
  rational mass-action Jacobian at the all-ones concentration with unit rate constants, as a
  `(numerator, denominator)` pair; `none` when there are no species. Negative exactly when the row
  diagonal-dominance test certifies the linearization there is Hurwitz (locally stable, no
  oscillation), in any number of species; the magnitude grades the stability robustness. It is a
  one-directional sufficient stability margin, not a full spectral verdict: it can fail for matrices
  that are nonetheless Hurwitz. -/
  gershgorinStabilityMargin : Option (Int × Int)
  /-- The column-form Gershgorin local-stability spectral margin `max_k ( J k k + ∑_{i≠k} |J i k| )`
  of the rational mass-action Jacobian at the all-ones concentration with unit rate constants, as a
  `(numerator, denominator)` pair; `none` when there are no species. Negative exactly when the column
  diagonal-dominance test certifies the linearization there is Hurwitz, in any number of species. It
  is the column companion of `gershgorinStabilityMargin`: the row and column tests are distinct
  sufficient conditions, so this is an independent stability certificate, not a full spectral
  verdict. -/
  gershgorinColStabilityMargin : Option (Int × Int)
  deriving FromJson, ToJson, Repr, DecidableEq

namespace NetworkData

/-- **Analyze a data-driven network**: compute its structural invariants in one record. -/
def analyze (d : NetworkData) : Analysis :=
  let N := d.toNetwork
  let acr : Array Nat := (((List.finRange d.numSpecies).filter
    (fun s => decide (N.HasShinarFeinbergPair s))).map Fin.val).toArray
  let ms : Array (Array Nat) := (((List.finRange d.numSpecies).sublists.filter
    (fun l => decide (N.IsMinimalSiphon l.toFinset))).map
    (fun l => (l.map Fin.val).toArray)).toArray
  { version := analysisVersion
    numSpecies := d.numSpecies
    numComplexes := N.numComplexes
    numReactions := N.numReactions
    numLinkageClasses := N.computeNumLinkageClasses
    numStrongLinkageClasses := N.numStrongLinkageClasses
    stoichRank := computeRank N.stoichMatrixQ
    conservationLawDim := d.numSpecies - computeRank N.stoichMatrixQ
    deficiency := N.computableDeficiency
    weaklyReversible := decide N.WeaklyReversible
    acrSpecies := acr
    hasSiphon := decide (∃ P : Finset (Fin d.numSpecies), P.Nonempty ∧ N.IsSiphon P)
    minimalSiphons := ms
    srSignConsistent := decide N.ConsistentSRSign
    srPMatrixPointIndep := decide N.ConsistentSRSign && decide N.ConsistentDiagonalDrive
    hasCriticalSiphon := decide N.HasCriticalSiphon
    persistenceStructural := decide N.WeaklyReversible && !decide N.HasCriticalSiphon
    persistenceCertified := decide N.WeaklyReversible && N.computableDeficiency == 0
      && !decide N.HasCriticalSiphon
    noPositivePeriodicOrbitCertified :=
      (decide N.WeaklyReversible && N.computableDeficiency == 0)
        || decide (computeRank N.stoichMatrixQ ≤ 1)
    stoichRankTwo := computeRank N.stoichMatrixQ == 2
    persistenceSingleLinkage := decide N.WeaklyReversible && N.computeNumLinkageClasses == 1
    noDrainableSiphon := decide N.HasNoDrainableSiphon
    noSelfReplicableSiphon := decide N.HasNoSelfReplicableSiphon
    minimalCriticalSiphonDichotomy := decide N.MinimalCriticalSiphonDichotomy
    persistenceSiphonDichotomy := decide N.WeaklyReversible
      && decide N.MinimalCriticalSiphonDichotomy
      && (decide N.HasNoDrainableSiphon || decide N.HasNoSelfReplicableSiphon)
    deficiencyOneConditions := decide N.DeficiencyOneConditions
    numMinimalSiphons := ms.size
    minSiphonSize := ms.foldl (fun m a => min m a.size) (d.numSpecies + 1)
    numACRSpecies := acr.size
    numTerminalSLC := N.computeNumTerminalSLC
    numDiagonalDriveSpecies := N.numDiagonalDriveSpecies
    hopfBoundaryMargin :=
      if h : d.numSpecies = 3 then
        let q := (h ▸ N : Network (Fin 3)).hopfBoundaryMarginQ
        some (q.num, (q.den : Int))
      else none
    gershgorinStabilityMargin :=
      if h : 0 < d.numSpecies then
        haveI : Nonempty (Fin d.numSpecies) := ⟨⟨0, h⟩⟩
        let q := N.gershgorinStabilityMarginQ
        some (q.num, (q.den : Int))
      else none
    gershgorinColStabilityMargin :=
      if h : 0 < d.numSpecies then
        haveI : Nonempty (Fin d.numSpecies) := ⟨⟨0, h⟩⟩
        let q := N.gershgorinColStabilityMarginQ
        some (q.num, (q.den : Int))
      else none }

/-- The reported deficiency is the network's deficiency. -/
theorem analyze_deficiency_eq (d : NetworkData) :
    (d.analyze).deficiency = d.toNetwork.deficiency :=
  (d.toNetwork.deficiency_eq_computableDeficiency).symm

/-- The reported stoichiometric rank is the network's stoichiometric rank. -/
theorem analyze_stoichRank_eq (d : NetworkData) :
    (d.analyze).stoichRank = d.toNetwork.stoichRank :=
  (d.toNetwork.stoichRank_eq_computeRank).symm

/-- The reported conservation-law dimension is the dimension of the conservation-law space:
the `orthSum` (dot-product complement) of the stoichiometric subspace. -/
theorem analyze_conservationLawDim_eq (d : NetworkData) :
    (d.analyze).conservationLawDim
      = Module.finrank ℝ (orthSum d.toNetwork.stoichSubspace) := by
  show d.numSpecies - computeRank d.toNetwork.stoichMatrixQ
    = Module.finrank ℝ (orthSum d.toNetwork.stoichSubspace)
  rw [finrank_orthSum, Fintype.card_fin, ← d.toNetwork.stoichRank_eq_computeRank]
  simp only [Network.stoichRank]

/-- The reported linkage-class count is the network's linkage-class count. -/
theorem analyze_numLinkageClasses_eq (d : NetworkData) :
    (d.analyze).numLinkageClasses = d.toNetwork.numLinkageClasses :=
  d.toNetwork.computeNumLinkageClasses_eq_numLinkageClasses

/-- The reported weak-reversibility flag is `true` exactly when the network is weakly reversible. -/
theorem analyze_weaklyReversible_eq (d : NetworkData) :
    (d.analyze).weaklyReversible = true ↔ d.toNetwork.WeaklyReversible :=
  decide_eq_true_iff

/-- A species index is reported in `acrSpecies` exactly when that species carries a structural
Shinar–Feinberg ACR witness. -/
theorem analyze_acrSpecies_eq (d : NetworkData) (s : Fin d.numSpecies) :
    s.val ∈ (d.analyze).acrSpecies ↔ d.toNetwork.HasShinarFeinbergPair s := by
  show s.val ∈ (((List.finRange d.numSpecies).filter
      (fun t => decide (d.toNetwork.HasShinarFeinbergPair t))).map Fin.val).toArray ↔ _
  simp only [List.mem_toArray, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hav⟩
    rwa [Fin.val_injective hav] at ha
  · intro h
    exact ⟨s, h, rfl⟩

/-- The reported siphon flag is `true` exactly when the network has a nonempty siphon. -/
theorem analyze_hasSiphon_eq (d : NetworkData) :
    (d.analyze).hasSiphon = true ↔
      ∃ P : Finset (Fin d.numSpecies), P.Nonempty ∧ d.toNetwork.IsSiphon P :=
  decide_eq_true_iff

/-- **Sound persistence filter.** When the siphon flag is `false`, the network has no critical
siphon (every critical siphon is a nonempty siphon), so with weak reversibility and complex
balancing it is persistent. The exclusion is Farkas-free — only the decidable `IsSiphon` is used. -/
theorem analyze_hasNoCriticalSiphon_of_hasSiphon_false (d : NetworkData)
    (h : (d.analyze).hasSiphon = false) : d.toNetwork.HasNoCriticalSiphon := by
  apply Network.hasNoCriticalSiphon_of_forall_not_isSiphon
  intro P hP hsiph
  have htrue : (d.analyze).hasSiphon = true := (analyze_hasSiphon_eq d).mpr ⟨P, hP, hsiph⟩
  simp [htrue] at h

/-- An entry of `minimalSiphons` is exactly the ascending index image of a minimal siphon: it is
present iff some subset list `l` of the species whose underlying set `l.toFinset` is a minimal
siphon maps to it. -/
theorem mem_analyze_minimalSiphons (d : NetworkData) (arr : Array Nat) :
    arr ∈ (d.analyze).minimalSiphons ↔
      ∃ l : List (Fin d.numSpecies), l ∈ (List.finRange d.numSpecies).sublists ∧
        d.toNetwork.IsMinimalSiphon l.toFinset ∧ arr = (l.map Fin.val).toArray := by
  show arr ∈ (((List.finRange d.numSpecies).sublists.filter
      (fun l => decide (d.toNetwork.IsMinimalSiphon l.toFinset))).map
      (fun l => (l.map Fin.val).toArray)).toArray ↔ _
  simp only [List.mem_toArray, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨l, ⟨hl, hmin⟩, harr⟩
    exact ⟨l, hl, hmin, harr.symm⟩
  · rintro ⟨l, hl, hmin, harr⟩
    exact ⟨l, ⟨hl, hmin⟩, harr.symm⟩

/-- The reported SR-sign-consistency flag is `true` exactly when the network satisfies the
consistent signed species–reaction cover condition. It exposes only the decidable sign fragment of
the Craciun–Feinberg injectivity criterion; the chart-box, positivity, and positive-diagonal
hypotheses for a full injectivity verdict are supplied by the consumer. -/
theorem analyze_srSignConsistent_eq (d : NetworkData) :
    (d.analyze).srSignConsistent = true ↔ d.toNetwork.ConsistentSRSign :=
  decide_eq_true_iff

/-- The reported point-independent P-matrix flag is `true` exactly when the network satisfies both
the consistent signed species–reaction cover condition and the per-species positive-diagonal-drive
condition (`ConsistentSRSign ∧ ConsistentDiagonalDrive`), the decidable point-free precondition of
the full-Jacobian P-matrix verdict. -/
theorem analyze_srPMatrixPointIndep_eq (d : NetworkData) :
    (d.analyze).srPMatrixPointIndep = true ↔
      d.toNetwork.ConsistentSRSign ∧ d.toNetwork.ConsistentDiagonalDrive := by
  show (decide d.toNetwork.ConsistentSRSign && decide d.toNetwork.ConsistentDiagonalDrive) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

/-- **Point-free full-Jacobian P-matrix verdict.** When the point-independent P-matrix flag is
`true`, the full mass-action Jacobian is a P-matrix at every positive concentration of any set, for
every positive rate constants — read off the signed species–reaction graph alone, with no per-point
hypothesis. This is the sound, decidable, point-free keystone of the Craciun–Feinberg injectivity
criterion. It is *not* a full injectivity verdict: carrying it to compatibility-class injectivity
needs a coordinate chart whose reduced Jacobian is a P-matrix on a box (a Schur-style oblique
compression that the full-Jacobian P-matrix property does not transport to by submatrix selection),
a hypothesis the consumer supplies to `massActionInjectiveOnClass_of_pivotReducedJacobian_pmatrix`. -/
theorem isPMatrix_massActionJacobian_box_of_srPMatrixPointIndep (d : NetworkData)
    (h : (d.analyze).srPMatrixPointIndep = true) (κ : d.toNetwork.RateConstants)
    (C : Set (Concentration (Fin d.numSpecies))) (hC : ∀ x ∈ C, x.Positive) :
    ∀ x ∈ C, (d.toNetwork.massActionJacobian κ x).IsPMatrix := by
  obtain ⟨hsign, hdrive⟩ := (analyze_srPMatrixPointIndep_eq d).mp h
  exact d.toNetwork.isPMatrix_massActionJacobian_box_of_decide κ C hC hsign hdrive

/-- The reported critical-siphon flag is `true` exactly when the network has a critical siphon: a
nonempty siphon carrying no positive conservation law on its exact support. The verdict is decided by
rational feasibility (Fourier–Motzkin elimination). When `false`, the network has no critical siphon,
so with weak reversibility and complex balancing it is persistent. -/
theorem analyze_hasCriticalSiphon_eq (d : NetworkData) :
    (d.analyze).hasCriticalSiphon = true ↔ d.toNetwork.HasCriticalSiphon :=
  decide_eq_true_iff

/-- The reported structural-persistence flag is `weaklyReversible ∧ ¬hasCriticalSiphon`. -/
theorem analyze_persistenceStructural_eq (d : NetworkData) :
    (d.analyze).persistenceStructural
      = ((d.analyze).weaklyReversible && !(d.analyze).hasCriticalSiphon) :=
  rfl

/-- **Structural persistence precondition.** When the structural-persistence flag is `true`, the
network is weakly reversible and has no critical siphon — the structural half of the global-attractor
persistence verdict's hypothesis. It is *not* a full persistence proof: the global-attraction
conclusion additionally needs a positive complex-balanced reference (supplied to
`gac_of_hasNoCriticalSiphon`), which the contract cannot certify from structure alone. -/
theorem hasNoCriticalSiphon_of_persistenceStructural (d : NetworkData)
    (h : (d.analyze).persistenceStructural = true) :
    d.toNetwork.WeaklyReversible ∧ d.toNetwork.HasNoCriticalSiphon := by
  rw [analyze_persistenceStructural_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨(analyze_weaklyReversible_eq d).mp h.1, ?_⟩
  rw [Network.hasNoCriticalSiphon_iff_not_hasCriticalSiphon, ← analyze_hasCriticalSiphon_eq d,
    h.2]
  exact Bool.false_ne_true

/-- The reported certified-persistence flag is
`weaklyReversible ∧ deficiency = 0 ∧ ¬hasCriticalSiphon`. -/
theorem analyze_persistenceCertified_eq (d : NetworkData) :
    (d.analyze).persistenceCertified
      = ((d.analyze).weaklyReversible && (d.analyze).deficiency == 0
          && !(d.analyze).hasCriticalSiphon) :=
  rfl

/-- **Certified structural precondition.** When the certified-persistence flag is `true`, the network
is weakly reversible, of deficiency zero, and has no critical siphon. These are exactly the structural
hypotheses of `gac_of_deficiencyZero_decide`: the complex-balanced reference is then supplied by the
Feinberg–Horn–Jackson deficiency-zero theorem, not by the consumer. -/
theorem certifiedHypotheses_of_persistenceCertified (d : NetworkData)
    (h : (d.analyze).persistenceCertified = true) :
    d.toNetwork.WeaklyReversible ∧ d.toNetwork.DeficiencyZero
      ∧ d.toNetwork.HasNoCriticalSiphon := by
  rw [analyze_persistenceCertified_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hwr, hδ⟩, hcs⟩ := h
  refine ⟨(analyze_weaklyReversible_eq d).mp hwr, ?_, ?_⟩
  · rw [Network.deficiencyZero_iff_computableDeficiency_eq_zero]
    exact beq_iff_eq.mp hδ
  · rw [Network.hasNoCriticalSiphon_iff_not_hasCriticalSiphon, ← analyze_hasCriticalSiphon_eq d, hcs]
    exact Bool.false_ne_true

/-- **Proof-carrying global persistence certificate from the analyzer.**  A true
`persistenceCertified` flag is not merely reported as a structural tuple: it constructs the new
strong `GlobalPersistenceCertificate`, valid for every positive rate vector and every positive
initial condition. -/
theorem globalPersistenceCertificate_of_persistenceCertified (d : NetworkData)
    (h : (d.analyze).persistenceCertified = true) :
    d.toNetwork.GlobalPersistenceCertificate := by
  obtain ⟨hwr, hδ, hncs⟩ := certifiedHypotheses_of_persistenceCertified d h
  exact Network.GlobalPersistenceCertificate.ofDeficiencyZeroNoCriticalSiphon
    d.toNetwork hwr hδ hncs

/-- **Certified global-attractor / no-extinction verdict.** When the certified-persistence flag is
`true`, the network is weakly reversible, of deficiency zero, and has no critical siphon. For any
positive rate constants and any positive start `x₀`, there is a positive complex-balanced
concentration `x*` in `x₀`'s compatibility class such that the mass-action semiflow through `x₀`
converges to it: its ω-limit set is exactly `{x*}`. The complex-balanced reference is supplied by the
deficiency-zero theorem; the only input the contract cannot certify is the positive start, a genuine
per-trajectory hypothesis. The verdict therefore reads: every positive trajectory converges to the
network's complex-balanced equilibrium in its own compatibility class. -/
theorem gac_of_persistenceCertified (d : NetworkData)
    (h : (d.analyze).persistenceCertified = true) (κ : d.toNetwork.RateConstants)
    {x₀ : Concentration (Fin d.numSpecies)} (hx0 : x₀.Positive) :
    ∃ xstar : Concentration (Fin d.numSpecies), xstar.Positive
      ∧ d.toNetwork.IsComplexBalanced κ xstar ∧ d.toNetwork.StoichCompatible x₀ xstar ∧
      ∃ (ϕ : Flow ℝ≥0 (Concentration (Fin d.numSpecies)))
        (γ : Concentration (Fin d.numSpecies) → ℝ → Concentration (Fin d.numSpecies)),
        (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
        (∀ t, 0 ≤ t →
          HasDerivAt (γ x₀) (d.toNetwork.massActionVectorField κ (γ x₀ t)) t) ∧
        omegaLimit Filter.atTop ϕ {x₀} = {xstar} := by
  obtain ⟨hwr, hδ, _⟩ := certifiedHypotheses_of_persistenceCertified d h
  have hcs : decide d.toNetwork.HasCriticalSiphon = false := by
    rw [analyze_persistenceCertified_eq, Bool.and_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at h
    exact h.2
  exact d.toNetwork.gac_of_deficiencyZero_decide hwr κ hδ hcs hx0

/-- The reported non-oscillation flag is the disjunction of the two currently compiled global
exclusion routes: weak reversibility plus deficiency zero, or stoichiometric rank at most one. -/
theorem analyze_noPositivePeriodicOrbitCertified_eq (d : NetworkData) :
    (d.analyze).noPositivePeriodicOrbitCertified
      = (((d.analyze).weaklyReversible && (d.analyze).deficiency == 0)
          || decide ((d.analyze).stoichRank ≤ 1)) :=
  rfl

/-- **Kernel bridge for the structural non-oscillation flag.**  When the compiled analyzer reports
`noPositivePeriodicOrbitCertified = true`, no positive rate constants on the reconstructed network
can admit a nonconstant positive periodic mass-action orbit.  The proof payload records whichever of
the deficiency-zero or low-rank routes discharged the claim. -/
theorem neverPositivePeriodic_of_analyze (d : NetworkData)
    (h : (d.analyze).noPositivePeriodicOrbitCertified = true) :
    d.toNetwork.NeverPositivePeriodic := by
  change ((decide d.toNetwork.WeaklyReversible
      && d.toNetwork.computableDeficiency == 0)
      || decide (computeRank d.toNetwork.stoichMatrixQ ≤ 1)) = true at h
  rw [Bool.or_eq_true] at h
  rcases h with hdz | hrank
  · rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hdz
    apply d.toNetwork.neverPositivePeriodic_of_weaklyReversible_deficiencyZero hdz.1
    rw [Network.deficiencyZero_iff_computableDeficiency_eq_zero]
    exact hdz.2
  · have hq : computeRank d.toNetwork.stoichMatrixQ ≤ 1 := of_decide_eq_true hrank
    apply d.toNetwork.neverPositivePeriodic_of_stoichRank_le_one
    rw [d.toNetwork.stoichRank_eq_computeRank]
    exact hq

/-- The rank-two flag is true exactly for stoichiometric rank two.  It is a route selector for planar
global-dynamics certificates, not itself an oscillation claim. -/
theorem analyze_stoichRankTwo_eq (d : NetworkData) :
    (d.analyze).stoichRankTwo = true ↔ d.toNetwork.stoichRank = 2 := by
  change (computeRank d.toNetwork.stoichMatrixQ == 2) = true ↔ _
  rw [beq_iff_eq, ← d.toNetwork.stoichRank_eq_computeRank]

/-- The reported single-linkage persistence flag is `weaklyReversible ∧ numLinkageClasses = 1`. -/
theorem analyze_persistenceSingleLinkage_eq (d : NetworkData) :
    (d.analyze).persistenceSingleLinkage
      = ((d.analyze).weaklyReversible && (d.analyze).numLinkageClasses == 1) :=
  rfl

/-- **Single-linkage persistence precondition.** When the single-linkage flag is `true`, the
network is weakly reversible and has one linkage class.  The library now proves these hypotheses
imply standard strong endotacticity; the flag therefore certifies the structural/geometric input to
the strongly-endotactic permanence theorem.  It is still not itself a persistence verdict until the
remaining analytic theorem `StronglyEndotacticStd → StructurallyPermanent` is formalized. -/
theorem singleLinkageHypotheses_of_persistenceSingleLinkage (d : NetworkData)
    (h : (d.analyze).persistenceSingleLinkage = true) :
    d.toNetwork.WeaklyReversible ∧ d.toNetwork.SingleLinkageClass := by
  rw [analyze_persistenceSingleLinkage_eq, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨(analyze_weaklyReversible_eq d).mp h.1, ?_⟩
  have h3 : d.toNetwork.computeNumLinkageClasses = 1 := h.2
  exact d.toNetwork.singleLinkageClass_of_computeNumLinkageClasses_eq_one h3

/-- **Proof-carrying strong-endotactic certificate from the single-linkage analyzer flag.**
The flag itself still does not assert persistence/permanence, because that requires the analytic
strong-endotactic permanence theorem.  What is now fully certified from structure is the exact
geometric hypothesis consumed by that theorem. -/
theorem strongEndotacticCertificate_of_persistenceSingleLinkage (d : NetworkData)
    (h : (d.analyze).persistenceSingleLinkage = true) :
    d.toNetwork.StrongEndotacticCertificate := by
  obtain ⟨hwr, hslc⟩ := singleLinkageHypotheses_of_persistenceSingleLinkage d h
  exact Network.StrongEndotacticCertificate.ofWeaklyReversibleSingleLinkage
    d.toNetwork hwr hslc


/-- **Single-linkage analyzer route to permanence.**  This constructor is deliberately
parameterized by the remaining analytic theorem instead of importing the research-frontier module.
Once `StronglyEndotacticStd → StructurallyPermanent` has been proved, every true single-linkage
flag upgrades automatically to a proof-carrying permanence certificate. -/
theorem globalPermanenceCertificate_of_persistenceSingleLinkage (d : NetworkData)
    (h : (d.analyze).persistenceSingleLinkage = true)
    (hperm : d.toNetwork.StronglyEndotacticStd → d.toNetwork.StructurallyPermanent) :
    d.toNetwork.GlobalPermanenceCertificate := by
  have hse : d.toNetwork.StronglyEndotacticStd :=
    (strongEndotacticCertificate_of_persistenceSingleLinkage d h).sound
  exact Network.GlobalPermanenceCertificate.ofProof d.toNetwork (hperm hse)

/-- The same analyzer route, projected to ordinary structural persistence. -/
theorem standardPersistenceCertificate_of_persistenceSingleLinkage (d : NetworkData)
    (h : (d.analyze).persistenceSingleLinkage = true)
    (hperm : d.toNetwork.StronglyEndotacticStd → d.toNetwork.StructurallyPermanent) :
    d.toNetwork.StandardPersistenceCertificate :=
  (globalPermanenceCertificate_of_persistenceSingleLinkage d h hperm).toStandardPersistence

/-- Exact analyzer reflection for the no-drainable-siphon verdict. -/
theorem analyze_noDrainableSiphon_eq (d : NetworkData) :
    (d.analyze).noDrainableSiphon = true ↔ d.toNetwork.HasNoDrainableSiphon :=
  decide_eq_true_iff

/-- Exact analyzer reflection for the non-autocatalytic siphon verdict. -/
theorem analyze_noSelfReplicableSiphon_eq (d : NetworkData) :
    (d.analyze).noSelfReplicableSiphon = true ↔ d.toNetwork.HasNoSelfReplicableSiphon :=
  decide_eq_true_iff

/-- A true no-drainable-siphon analyzer verdict now produces a complete clean
omega-persistence certificate directly; the minimal-critical-siphon dichotomy is not needed. -/
theorem omegaPersistenceCertificate_of_noDrainableSiphon (d : NetworkData)
    (h : (d.analyze).noDrainableSiphon = true) :
    d.toNetwork.OmegaPersistenceCertificate :=
  Network.OmegaPersistenceCertificate.ofNoDrainableSiphon d.toNetwork
    ((analyze_noDrainableSiphon_eq d).mp h)

/-- A weakly-reversible network with no self-replicable siphon has a complete clean
omega-persistence certificate. -/
theorem omegaPersistenceCertificate_of_noSelfReplicableSiphon (d : NetworkData)
    (hwrB : (d.analyze).weaklyReversible = true)
    (h : (d.analyze).noSelfReplicableSiphon = true) :
    d.toNetwork.OmegaPersistenceCertificate :=
  Network.OmegaPersistenceCertificate.ofWeaklyReversibleNoSelfReplicable d.toNetwork
    ((analyze_weaklyReversible_eq d).mp hwrB)
    ((analyze_noSelfReplicableSiphon_eq d).mp h)

/-- Exact analyzer reflection for the per-network minimal-critical-siphon dichotomy. -/
theorem analyze_minimalCriticalSiphonDichotomy_eq (d : NetworkData) :
    (d.analyze).minimalCriticalSiphonDichotomy = true ↔
      d.toNetwork.MinimalCriticalSiphonDichotomy :=
  decide_eq_true_iff

/-- The new siphon-dichotomy persistence flag is exactly its four structural booleans. -/
theorem analyze_persistenceSiphonDichotomy_eq (d : NetworkData) :
    (d.analyze).persistenceSiphonDichotomy =
      ((d.analyze).weaklyReversible && (d.analyze).minimalCriticalSiphonDichotomy &&
        ((d.analyze).noDrainableSiphon || (d.analyze).noSelfReplicableSiphon)) :=
  rfl

/-- A true siphon-dichotomy flag constructs an actual global boundary-omega certificate.  This is
proof producing even though the *universal* minimal-critical-siphon theorem has not yet been proved:
the analyzer has verified the finite proposition for this particular network. -/
theorem boundaryOmegaCertificate_of_persistenceSiphonDichotomy (d : NetworkData)
    (h : (d.analyze).persistenceSiphonDichotomy = true) :
    d.toNetwork.BoundaryOmegaCertificate := by
  rw [analyze_persistenceSiphonDichotomy_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨hwrB, hdichB⟩, hsign⟩ := h
  have hwr : d.toNetwork.WeaklyReversible := (analyze_weaklyReversible_eq d).mp hwrB
  have hdich : d.toNetwork.MinimalCriticalSiphonDichotomy :=
    (analyze_minimalCriticalSiphonDichotomy_eq d).mp hdichB
  rcases hsign with hndB | hnsrB
  · have hnd : d.toNetwork.HasNoDrainableSiphon :=
      (analyze_noDrainableSiphon_eq d).mp hndB
    exact Network.BoundaryOmegaCertificate.ofWeaklyReversibleNoDrainable
      d.toNetwork hdich hwr hnd
  · have hnsr : d.toNetwork.HasNoSelfReplicableSiphon :=
      (analyze_noSelfReplicableSiphon_eq d).mp hnsrB
    exact Network.BoundaryOmegaCertificate.ofWeaklyReversibleNoSelfReplicable
      d.toNetwork hdich hwr hnsr

/-- The reported deficiency-one-conditions flag decides `DeficiencyOneConditions`. -/
theorem analyze_deficiencyOneConditions_eq (d : NetworkData) :
    (d.analyze).deficiencyOneConditions = decide d.toNetwork.DeficiencyOneConditions :=
  rfl

/-- **Deficiency-one linkage conditions.** When the flag is `true`, the network satisfies conditions
(i) and (ii) of Feinberg's deficiency-one theorem: every linkage class has deficiency at most one and
the per-class deficiencies sum to the network deficiency. A full deficiency-one verdict additionally
requires each linkage class to have exactly one terminal strong linkage class. -/
theorem deficiencyOneConditions_of_analyze (d : NetworkData)
    (h : (d.analyze).deficiencyOneConditions = true) :
    d.toNetwork.DeficiencyOneConditions :=
  of_decide_eq_true h

/-- The reported strong-linkage-class count is the network's strong-linkage-class count. -/
theorem analyze_numStrongLinkageClasses_eq (d : NetworkData) :
    (d.analyze).numStrongLinkageClasses = d.toNetwork.numStrongLinkageClasses :=
  rfl

/-- The reported terminal-strong-linkage-class count is the network's terminal-SLC count `t`. -/
theorem analyze_numTerminalSLC_eq (d : NetworkData) :
    (d.analyze).numTerminalSLC = d.toNetwork.numTerminalSLC :=
  d.toNetwork.computeNumTerminalSLC_eq_numTerminalSLC

/-- The reported diagonal-drive species count is the network's diagonal-drive species count. -/
theorem analyze_numDiagonalDriveSpecies_eq (d : NetworkData) :
    (d.analyze).numDiagonalDriveSpecies = d.toNetwork.numDiagonalDriveSpecies := rfl

/-- **Graded injectivity precondition.** The diagonal-drive species count equals the species count
exactly when every species is positively driven, i.e. the network satisfies `ConsistentDiagonalDrive`
— the per-species half of the point-free P-matrix injectivity precondition. -/
theorem analyze_numDiagonalDriveSpecies_eq_card_iff (d : NetworkData) :
    (d.analyze).numDiagonalDriveSpecies = d.numSpecies ↔ d.toNetwork.ConsistentDiagonalDrive := by
  have key := d.toNetwork.numDiagonalDriveSpecies_eq_card_iff
  rw [Fintype.card_fin] at key
  exact key

/-- The Hopf-boundary margin is `none` for any network whose species count is not three: the cubic
Routh–Hurwitz Hopf-boundary combination is defined only in dimension three. -/
theorem analyze_hopfBoundaryMargin_eq_none_of_ne_three (d : NetworkData)
    (h : d.numSpecies ≠ 3) : (d.analyze).hopfBoundaryMargin = none := by
  simp only [analyze, dif_neg h]

/-- The Gershgorin stability margin is `none` for a network with no species: the worst-row maximum is
taken over an empty index set. For any network with at least one species the field is a `some` pair. -/
theorem analyze_gershgorinStabilityMargin_eq_none_of_zero_species (d : NetworkData)
    (h : d.numSpecies = 0) : (d.analyze).gershgorinStabilityMargin = none := by
  have hlt : ¬ 0 < d.numSpecies := by omega
  simp only [analyze, dif_neg hlt]

/-- The column-form Gershgorin stability margin is `none` for a network with no species: the
worst-column maximum is taken over an empty index set. For any network with at least one species the
field is a `some` pair. -/
theorem analyze_gershgorinColStabilityMargin_eq_none_of_zero_species (d : NetworkData)
    (h : d.numSpecies = 0) : (d.analyze).gershgorinColStabilityMargin = none := by
  have hlt : ¬ 0 < d.numSpecies := by omega
  simp only [analyze, dif_neg hlt]

end NetworkData

end CRNT
