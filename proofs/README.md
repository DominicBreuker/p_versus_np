# Proof Workspace

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](p_versus_np/) | [circuit-lower-bounds](p_versus_np/circuit-lower-bounds/) | 90 | Active — direct but still highly incomplete route to `P ≠ NP`; present Lean progress is a conditional reduction plus partial counting infrastructure | Direct attack on `P ≠ NP`; the support track exists only to finish reusable circuit-model infrastructure |
| [p_subset_np](p_subset_np/) | [circuit-lifting](p_subset_np/circuit-lifting/) | 60 | Active — necessary support track; remaining work is standard verifier-lifting formalization in the same circuit model | Supports `p_versus_np/circuit-lower-bounds` by proving the easy inclusion `P ⊆ NP` and avoiding duplicate bookkeeping in the main route |

## Guidance for Researchers

Researchers work on one `proofs/PROBLEM/APPROACH` target per run.
The target is chosen randomly, with probability proportional to the numerical priority in the table above.
Every kept target must either be the main P vs NP proof or a documented material subproblem that helps the main proof.

## Guidance for the Project Leader

- Maintain this table and keep it ordered by descending priority.
- Maintain the `Relationships` column; it is required documentation, not optional commentary.
- Create a new `proofs/<problem>/` folder only when solving that problem would be a material step forward for an already-existing P vs NP proof approach.
- Create a new `proofs/<problem>/<approach>/` folder only when that approach clearly advances the associated problem.
- If the current active tracks still have concrete next lemmas, prefer tightening guidance over adding another route.
- Remove or retire proof tracks that no longer have a clear relationship to solving P vs NP.
- Keep `proofs/<problem>/README.md` current for each active problem.
- Review `references/README.md` and any relevant reference documents on each run.
