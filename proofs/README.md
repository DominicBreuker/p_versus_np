# Proof Workspace

| Problem | Approach | Priority | Status |
|---------|----------|----------|--------|
| [p_versus_np](p_versus_np/) | [circuit-lower-bounds](p_versus_np/circuit-lower-bounds/) | 90 | Active — conditional P ≠ NP proof exists; Shannon counting argument remains open |
| [p_subset_np](p_subset_np/) | [circuit-lifting](p_subset_np/circuit-lifting/) | 80 | Active — foundational theorem with a promising formal proof plan |
| [deterministic_time_hierarchy_theorem](deterministic_time_hierarchy_theorem/) | [diagonalization](deterministic_time_hierarchy_theorem/diagonalization/) | 70 | Active — monotonicity proven; diagonalization still blocked |

## Guidance for Researchers

Researchers work on one `proofs/PROBLEM/APPROACH` target per run.
The target is chosen randomly, with probability proportional to the numerical priority in the table above.

## Guidance for the Project Leader

- Maintain this table and keep it ordered by descending priority.
- Create new problem folders under `proofs/<problem>/` when a subproblem deserves dedicated treatment.
- Create new approach folders under `proofs/<problem>/<approach>/` when a fresh line of attack is worth exploring.
- Keep `proofs/<problem>/README.md` current for each active problem.
- Review `references/README.md` and any relevant reference documents on each run.
