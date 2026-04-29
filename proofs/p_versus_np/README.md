# Problem: P versus NP

Formally settle the relationship between `P` and `NP` in Lean4.
This is the main problem the repository exists to solve.

| Approach | Priority | Status | Relationships |
|----------|----------|--------|---------------|
| [circuit-lower-bounds](circuit-lower-bounds/) | 90 | Active — main route toward a formal `P ≠ NP` proof; current Lean work is still on the counting infrastructure and conditional reduction | Main proof track |

## Project-Leader Notes

- Keep this folder focused on approaches that directly attack `P = NP` or `P ≠ NP`.
- If a supporting subproblem is spun out into its own `proofs/<problem>/...` folder, document that relationship here and in the global table.
- Do not dilute this folder with side problems that are interesting but not materially useful for the current P vs NP routes.
