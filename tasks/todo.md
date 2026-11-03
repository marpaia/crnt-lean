# Expansion tasks

- [x] Stochastic: `DirichletForm.lean` proves the enabled-edge reversal, finite-region generator
  energy identity and symmetry, general nonnegative energy, and conserved-observable zero energy.
  Focused check and eight principal axiom guards pass.
- [x] Realization: `SourceCoefficientCompleteness.lean` proves coefficient extraction, necessity
  from equality on all or positive concentrations, complete finite-union certificates and mismatch
  witnesses. Focused check and six principal axiom guards pass.
- [x] Deficiency/decomposition: `RelationSpace.lean` constructs both block-relation spaces, proves
  rank-nullity, signed deficiency balance, independence characterizations, exact additivity and
  sharp inequality cases. Focused check and eight principal axiom guards pass.
- [x] First partial integration: `lake build +CRNT test.AxiomAudit CRNTFrontier Scaffold` passes
  (4,660 jobs); source-integrity checks pass and the reserved hole file is unchanged.
- [x] Concurrent-source integration: user's `cb62825` additions preserved by clean rebase;
  `lake build +CRNT test CRNTFrontier Scaffold` passes (4,691 jobs), pushed at `28d6549`.
- [x] Stochastic integration: `lake build +CRNT test CRNTFrontier Scaffold` passes
  (4,692 jobs), including all 22 newly added principal axiom guards.
- [ ] Checkpoint: independent mathematical review, public import integration, axiom audit.
- [ ] Checkpoint: integration builds, unchanged reserved hole, integrity scripts, verified commit/push.
- [ ] Next round: select broader results from the resulting mathematical dependency map.

## Broader slices now selected

- [x] `RelationMap.lean`: constructs the canonical complex-map action, its kernel, local
  deficiency products and sum, and proves global deficiency equals that sum iff the relation map
  is onto. Independent focused check plus six principal guards and integration pass (4,693 jobs).
- [ ] `FixedComplexRealization.lean`: construct a network on prescribed complexes from positive
  supported channel weights and prove its coefficient formula/realization criterion.
- [ ] After `DirichletForm.lean`: characterize zero energy by enabled-edge increments and
  communicating-class constancy, with positivity discharged from rates and concentrations.
- [ ] Next decomposition layer: exact sequence/cokernel identifying deficiency not assembled
  from blocks; survey for duplicates before implementing.

The partial integration builds the public core import closure. `DirichletForm` is now included;
the broader in-progress modules remain outside that closure until checked. The full-library
expansion build remains a later gate.
