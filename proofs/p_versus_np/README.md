# Problem: P versus NP

Formally settle the relationship between `P` and `NP` in Lean4.
This is the main problem the repository exists to solve.

| Approach | Priority | Status | Relationships |
|----------|----------|--------|---------------|
| [circuit-lower-bounds](circuit-lower-bounds/) | 90 | Active — Task 6 complete; Task 7 in progress; **3 `sorry`s remain** (`evalCircuit_normalizeCircuit` line 389; `poly_quadratic_bound_k_ge_1` line 797; pigeonhole step line 1140); `evalNode_normalizeNodeCode` closed 2026-04-30; `p_neq_np` compiles conditionally on two axioms | Main proof track; supporting work under `proofs/p_subset_np/` is now complete and frozen |

## Project-Leader Notes

- Keep this folder focused on approaches that directly attack `P = NP` or `P ≠ NP`.
- If a supporting subproblem is spun out into its own `proofs/<problem>/...` folder, document that relationship here and in the global table.
- Do not dilute this folder with side problems that are interesting but not materially useful for the current P vs NP routes.
- No additional direct approach was added in this review because `circuit-lower-bounds` still has concrete next proof obligations; keeping focus is more valuable than adding speculative alternatives. The `p_subset_np/circuit-lifting` support track is now complete.
