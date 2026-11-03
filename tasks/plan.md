# Fundamental and frontier CRNT expansion

Start: `origin/wt/holes-20261010-a`, `99c61ccb9b2e07df18e9c92c9e92be9887d27c3e`.
Work in this isolated checkout; periodically push verified commits to the requested branch.

The objective is a comprehensive fundamental CRNT library, extending into frontier mathematics.
This is an ongoing program, not a claim that every CRNT theorem or open problem is already solved.
The existing high-codimension siphon-face proof hole is reserved for the user.

## Architecture and acceptance

- Reuse the existing Network, kinetics, stoichiometry, and stochastic definitions.
- Check for existing results before choosing a new theorem; duplicate wrappers are not progress.
- Add complete mathematical slices in dedicated modules, with clear hypotheses and documentation.
- No new sorry/admit/axiom, unchecked implementation substitution, weakened contracts, or exclusions.
- Each slice requires focused elaboration, a nonvacuity/specialization check where meaningful,
  and `#print axioms` on its principal results. No new theorem may depend on `sorryAx`.
- Agents own disjoint files. The orchestrator owns imports, integration, commits, and pushes.
- Refresh the remote before pushing; preserve concurrent work and never force push.

## Ordered tasks

1. Survey and extend fundamental stochastic reaction dynamics.
2. Survey and extend realization/dynamical-equivalence theory.
3. Survey and extend deficiency/flux structure.
4. Independently review each slice and integrate its public imports and audits.
5. Build integration targets and run repository integrity checks; commit and push a verified batch.
6. Use the resulting dependency map to select progressively broader theorem families.

Tasks 1-3 are independent. Task 4 depends on each corresponding slice; task 5 follows integration.
New theorem targets and evidence are recorded in `tasks/todo.md` as the survey resolves them.

## Risks

Frontier theorem hypotheses can accidentally restate their conclusion; review their mathematical
content, not just elaboration. Existing umbrella imports include the reserved hole, so audit theorem
dependencies individually. Reused build artifacts are acceleration only; final Lake builds must
reconcile artifacts with the isolated source. Established results and unresolved mathematics must
remain distinguished. Preserve the dirty source worktree at `/private/tmp/crnt-holes-20261010-a`.
