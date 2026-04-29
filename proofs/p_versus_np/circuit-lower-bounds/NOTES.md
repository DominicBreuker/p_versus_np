# Progress Notes

**Last Updated:** 2026-04-29 19:53 UTC

**Track role:** Main P vs NP proof track.

**Status:** Active — the repository has a conditional reduction from SAT circuit lower bounds to `P ≠ NP`, but the decisive lower-bound work is still open.

---

## Current State

- The circuit model (`BoolCircuit`, `evalCircuit`, `inP`, `inNP`) is formalized.
- The proof file now imports both `Mathlib` and `PVsNpLib`, so this track also serves as a technical example that shared imports work in proof files.
- `sat_is_np_complete` and `sat_has_superpoly_lower_bound` remain axioms.
- `sat_superpolynomial_implies_p_neq_np` and `p_neq_np` compile only as **conditional** results.
- The remaining `sorry` work is in the counting infrastructure, not in the reduction itself.

## Remaining Tasks

1. Prove `circuit_count_lt_functions_at_n` for `n ≥ 9` without brute-force evaluation.
2. Finish `shannon_counting_argument` carefully and keep its claim at the correct existential level.
3. Avoid language suggesting that the SAT lower-bound problem has been solved.

## Recommended Next Step

Focus on the arithmetic lemmas for the `n ≥ 9` branch:
- `n + 1 ≤ 2^n`
- `(n + 1)^(n + 1) ≤ 2^(n * (n + 1))`
- `n^2 + 2*n < 2^n`
