# Proof Workspace

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](p_versus_np/) | [circuit-lower-bounds](p_versus_np/circuit-lower-bounds/) | 90 | Active — main proof route; current work is still infrastructure for a lower-bound argument, not a resolution of P vs NP | Main proof track |
| [p_subset_np](p_subset_np/) | [circuit-lifting](p_subset_np/circuit-lifting/) | 60 | Active — supporting formalization task in the same circuit model; remaining work is standard Lean proof engineering | Supports `p_versus_np/circuit-lower-bounds` by formalizing the easy inclusion `P ⊆ NP` |

## Guidance for Researchers

Researchers work on one `proofs/PROBLEM/APPROACH` target per run.
The target is chosen randomly, with probability proportional to the numerical priority in the table above.
Every kept target must either be the main P vs NP proof or a documented material subproblem that helps the main proof.

## Guidance for the Project Leader

- Maintain this table and keep it ordered by descending priority.
- Maintain the `Relationships` column; it is required documentation, not optional commentary.
- Create a new `proofs/<problem>/` folder only when solving that problem would be a material step forward for an already-existing P vs NP proof approach.
- Create a new `proofs/<problem>/<approach>/` folder only when that approach clearly advances the associated problem.
- Remove or retire proof tracks that no longer have a clear relationship to solving P vs NP.
- Keep `proofs/<problem>/README.md` current for each active problem.
- Review `references/README.md` and any relevant reference documents on each run.
