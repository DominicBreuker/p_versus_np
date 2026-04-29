# Problem: P versus NP

Formally settle the relationship between `P` and `NP` in Lean4.
This is the main problem the repository exists to solve.

| Approach | Priority | Status | Relationships |
|----------|----------|--------|---------------|
| [circuit-lower-bounds](circuit-lower-bounds/) | 90 | Active — direct but still highly incomplete route toward `P ≠ NP`; current Lean work is still on the conditional reduction and counting infrastructure | Main proof track; supporting work under `proofs/p_subset_np/` exists only to complete the shared circuit model this route reuses |

## Project-Leader Notes

- Keep this folder focused on approaches that directly attack `P = NP` or `P ≠ NP`.
- If a supporting subproblem is spun out into its own `proofs/<problem>/...` folder, document that relationship here and in the global table.
- Do not dilute this folder with side problems that are interesting but not materially useful for the current P vs NP routes.
- No additional direct approach was added in this review because `circuit-lower-bounds` still has concrete next proof obligations; keeping focus is more valuable than adding speculative alternatives.
