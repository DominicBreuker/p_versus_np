# Progress Notes

**Last Updated:** 2026-04-29 20:32:40 UTC

**Track role:** Main P vs NP proof track.

**Status:** Active — the repository has a conditional reduction from SAT circuit lower bounds to `P ≠ NP`, but the decisive lower-bound work is still open.

---

## Current State

- The circuit model (`BoolCircuit`, `evalCircuit`, `inP`, `inNP`) is formalized.
- The proof file now imports both `Mathlib` and `PVsNpLib`, so this track also serves as a technical example that shared imports work in proof files.
- `sat_is_np_complete` and `sat_has_superpoly_lower_bound` remain axioms.
- `sat_superpolynomial_implies_p_neq_np` and `p_neq_np` compile only as **conditional** results.
- **Task 6 COMPLETED:** `circuit_count_lt_functions_at_n` now compiles for all `n ≥ 4` without `sorry`, using three helper lemmas:
  - `n_plus_one_le_two_pow_n`: For `n ≥ 1`, `n + 1 ≤ 2^n`
  - `n_plus_one_pow_le_two_pow_n_times_n_plus_one`: For `n ≥ 1`, `(n + 1)^(n + 1) ≤ 2^(n * (n + 1))`
  - `n_squared_plus_two_n_lt_two_pow_n`: For `n ≥ 9`, `n^2 + 2*n < 2^n`
- The remaining `sorry` is in `shannon_counting_argument` (Task 7).

## Remaining Tasks

1. ~~Prove `circuit_count_lt_functions_at_n` for `n ≥ 9` without brute-force evaluation.~~ **DONE**
2. Finish `shannon_counting_argument` carefully and keep its claim at the correct existential level.
   - Need to show that for any polynomial `p`, eventually `p n < 2^n`
   - Then show `circuit_count_upper_bound n (p n) < boolean_function_count n`
3. Avoid language suggesting that the SAT lower-bound problem has been solved.

## Recommended Next Step

Focus on Task 7: Complete `shannon_counting_argument`.

The current blocker is showing that for any polynomial `p n = c * n^k + c`, eventually:
`(p n + 1)^(p n + 1) * 2^(p n) < 2^(2^n)`

This requires proving that the exponent `n * (p n + 1) + p n` is eventually less than `2^n`.
Since `p n = O(n^k)` and `2^n` grows exponentially, this holds for sufficiently large `n`.

Approach:
1. Add a helper lemma: for any `k, c`, eventually `c * n^k * log(n) < 2^n / 2`
2. Use this to bound `n * (p n + 1) + p n = O(n^k * n) = O(n^(k+1)) < 2^n`
3. Apply `Nat.pow_lt_pow_right` to conclude
4. Use pigeonhole principle: since there are more Boolean functions (2^(2^n)) than circuits of size ≤ p n, some function requires larger circuits

Note: The current `circuit_count_upper_bound` definition uses a rough bound `(s+1)^(s+1) * 2^s`.
For the Shannon argument to work cleanly, we may want to refine this bound or add a separate lemma for the sum over all sizes ≤ s.
