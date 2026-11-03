# Global persistence and permanence

This document describes the global-claim layer added on top of the original pointwise
persistence/GAC development.

## Quantifier hierarchy

The original `Network.PersistentFrom κ x₀` remains the strong, pointwise certificate consumed
by the GAC reduction.  The new API makes the quantifier level explicit:

- `PersistentForRates N κ`: every positive initial condition has `PersistentFrom κ`;
- `StructurallyPersistent N`: the previous statement holds for every rate vector;
- `BoundaryOmegaExcluded N κ`: every omega-limit point of every bounded positive genuine
  mass-action orbit satisfying the standard invariance hypotheses is positive;
- `StructurallyBoundaryOmegaExcluded N`: boundary exclusion for every rate vector;
- `PermanentForFlow`, `PermanentForRates`, and `StructurallyPermanent`: the corresponding
  quantified permanence interfaces.

The distinction is intentional.  `BoundaryOmegaExcluded` is the natural omega-limit
formulation produced by the existing siphon theory, while `PersistentFrom` also packages a
compact positive confining set and is therefore stronger.

## Unconditional theorem now exposed globally

The existing no-critical-siphon proof has been lifted to a global theorem:

```lean
theorem structurallyBoundaryOmegaExcluded_of_hasNoCriticalSiphon
    (N : Network S) (hncs : N.HasNoCriticalSiphon) :
    N.StructurallyBoundaryOmegaExcluded
```

No persistence premise is passed into this theorem.

## Endotactic geometry

`Geometry/EndotacticGlobal.lean` introduces `StronglyEndotacticStd`, whose strict condition is
triggered by a direction that is nonzero on at least one reaction vector.  This is the
finite-generator form of the usual condition `w ∉ S^⊥`.

The existing source-nonconstant definition is retained for compatibility.  The new module
proves:

```lean
WeaklyReversible.endotactic
StronglyEndotactic.toStd_of_weaklyReversible
```

Thus existing developments are not silently reinterpreted while new global claims can target
the standard stoichiometric formulation.

## Siphon autocatalysis layer

`Dynamics/SiphonAutocatalysis.lean` adds exact finite reaction-pathway definitions of:

- drainable species sets and drainable siphons;
- self-replicable species sets and self-replicable siphons;
- minimal critical siphons;
- the named theorem contracts for the minimal-critical-siphon dichotomy, no-drainable-siphon
  persistence, and non-autocatalytic weakly-reversible persistence.

The theorem contracts are ordinary `Prop` definitions, **not axioms**.  They make the remaining
published proof obligations explicit without making an unproved theorem available to Lean.

## Tier layer

`Dynamics/TierPersistence.lean` installs the core definitions needed for the deterministic tier
route to strongly-endotactic permanence:

- mass-action monomial comparison;
- same-tier and strict-tier relations;
- positive escaping tier sequences;
- proper and transversal tier sequences;
- top source tier and tier-descending sequences;
- the global `TierDescending` property.

The two hard literature-level steps were named as proof obligations:

```lean
StrongEndotacticTierCharacterizationClaim N
TierDescendingPermanenceClaim N
```

Both are now theorems: `stronglyEndotacticStd_iff_tierDescending` and
`tierDescendingPermanenceClaim` (`Persistence/StronglyEndotacticPermanence.lean`; the persistence
step is in `Persistence/StronglyEndotacticPersistence.lean`).

## Frontier discipline

`Dynamics/GlobalPersistenceFrontier.lean` names the unresolved or not-yet-formalized global
statements rather than installing them as assumptions.  In particular:

```lean
PersistenceConjectureStrong N
PersistenceConjectureOmega N
```

remain propositions to prove.  This keeps the open weak-reversibility persistence conjecture
separate from the classes that are already certified.

`GlobalPersistenceCertificate N` is proof-carrying: constructing one requires an actual proof
of `N.StructurallyPersistent`; it is not a boolean recognizer and cannot manufacture a theorem
from a successful heuristic check.

## Next proof obligations

The intended order is:

1. prove the single-linkage graph-to-strong-endotactic structural bridge;
2. prove the tier characterization of standard strong endotacticity;
3. formalize the entropy/dissipation and compact-absorption argument yielding permanence;
4. derive single-linkage weakly-reversible permanence/persistence as a corollary;
5. prove the minimal-critical-siphon drainable/self-replicable dichotomy;
6. prove no-drainable-siphon persistence and non-autocatalytic weakly-reversible persistence;
7. add further known low-dimensional global classes without conflating them with the general
   Persistence Conjecture.

The reusable downstream GAC theorem is already present as
`gac_of_structurallyPersistent`.

## Proof-carrying certificates

Two certificate levels are intentionally distinct:

- `BoundaryOmegaCertificate N` carries `StructurallyBoundaryOmegaExcluded N` and has a proved
  constructor `ofNoCriticalSiphon`;
- `GlobalPersistenceCertificate N` carries the stronger `StructurallyPersistent N` compact-interior
  certificate;
- `GlobalPermanenceCertificate N` carries `StructurallyPermanent N`.

This prevents a decidable structural filter from being mislabeled as a proof of a stronger dynamical
statement than the formal development currently establishes.


## Flow-based definitions are vacuous without a global flow

`IsMassActionFlow κ ϕ γ` requires a flow on all of `ℝ^S` whose curves solve the mass-action
equations from every initial point, including points outside the nonnegative orthant. For networks
with a reaction consuming a species with molecularity at least two this fails: for `2X → 0`,
`x' = −2κ x²` blows up in finite time from `x(0) = −1` (`CRNT.Examples.FlowVacuity.no_massActionFlow`).
Every flow-based property (`StructurallyPersistentStd`, `StructurallyPermanent`, and hence
`PersistenceConjecture`) then holds vacuously, although the positive solutions of `2X → 0` tend to
`0` (`CRNT.Examples.FlowVacuity.not_structurallyPersistent`). Results whose conclusion is one of
these flow-based properties should be read together with their trajectory-based counterparts:
`PersistentFrom` / `StructurallyPersistent`, `GenuinePermanentOnPositiveClass` /
`GenuinePermanentForRates`.
