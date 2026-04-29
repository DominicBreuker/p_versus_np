# Progress Notes

**Last Updated:** 2026-04-29 23:15:00 UTC

**Track role:** Main P vs NP proof track.

**Status:** Active — the repository has a conditional reduction from SAT circuit lower bounds to `P ≠ NP`, Task 6 is complete, and Task 7 has been significantly advanced with the k=0 case now fully complete.

---

## Current State

- The circuit model (`BoolCircuit`, `evalCircuit`, `inP`, `inNP`) is formalized.
- The proof file imports both `Mathlib` and `PVsNpLib`, so this track also serves as a technical example that shared imports work in proof files.
- `sat_is_np_complete` and `sat_has_superpoly_lower_bound` remain axioms.
- `sat_superpolynomial_implies_p_neq_np` and `p_neq_np` compile as **conditional** results.
- **Task 6 COMPLETED:** `circuit_count_lt_functions_at_n` now compiles for all `n ≥ 4` without `sorry`, using helper lemmas for polynomial vs exponential bounds.
- **Task 7 PROGRESS:** `shannon_counting_argument` structure is in place with `poly_quadratic_bound` significantly advanced.

## Remaining Tasks

1. ~~Prove `circuit_count_lt_functions_at_n` for `n ≥ 9` without brute-force evaluation.~~ **DONE**
2. Finish `shannon_counting_argument` (Task 7).
   - **Status:** Proof structure is significantly advanced. Two `sorry`s remain:
     - `poly_quadratic_bound_k_ge_1` (line 272): Need to prove the general polynomial vs exponential bound for k ≥ 1.
     - Final step in `shannon_counting_argument` (line 540): Need to formalize the pigeonhole principle conclusion.

## What Was Changed in This Session

### Files Modified
- `proofs/p_versus_np/circuit-lower-bounds/Proof.lean`:
  - Added `four_n_squared_plus_six_n_plus_one_lt_two_pow_n`: Helper lemma proving `4*n^2 + 6*n + 1 < 2^n` for `n ≥ 196` using induction.
  - Added `poly_quadratic_bound_k0`: Helper lemma proving `4*c^2 + 6*c + 1 < 2^n` for `n ≥ 2*c + 5` using induction on c.
  - Added `poly_quadratic_bound_k_ge_1`: Helper lemma for the k ≥ 1 case (currently uses sorry for the general polynomial vs exponential bound).
  - **COMPLETED the k=0 case of `poly_quadratic_bound`**: Both c ≤ 95 (using `poly_quadratic_bound_k0`) and c > 95 (using `four_n_squared_plus_six_n_plus_one_lt_two_pow_n`) are now proven.
  - Updated `poly_quadratic_bound` to handle k=0 completely and k ≥ 1 using `poly_quadratic_bound_k_ge_1`.
  - Simplified `poly_quadratic_bound` to use threshold `n ≥ 100*k + c + 100`.
  - Updated `shannon_counting_argument` to use the new threshold.

### Key Insights
- The counting argument for general polynomials follows the same structure as for the identity polynomial (Task 6).
- The main technical challenge is formalizing that exponential growth (2^n) eventually dominates polynomial growth (n^(2k)).
- Using a larger threshold (100*k + c + 100) avoids the need for complex arithmetic proofs while maintaining mathematical correctness.
- The pigeonhole principle step requires formalizing cardinality arguments in Lean, which needs additional infrastructure.
- The new helper lemmas `poly_quadratic_bound_k0` and `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` successfully prove the k=0 case completely, demonstrating that the induction approach works for polynomial vs exponential bounds.
- The k=0 case of `poly_quadratic_bound` is now **fully complete** with no sorries.

## Recommended Next Step

Focus on completing `poly_quadratic_bound_k_ge_1` (the k ≥ 1 case).

**Approach:** The k=0 case is now **fully complete**. The remaining work is:

1. **Complete `poly_quadratic_bound_k_ge_1`:** Prove that for k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100, we have `(c * n^k + 2*c)^2 + 3*(c * n^k + 2*c) + 1 < 2^n`.
   - The threshold n ≥ 100*k + c + 100 ensures n is sufficiently large (n ≥ 200 for k ≥ 1, c ≥ 1).
   - For such large n, 2^n grows exponentially while the left side grows polynomially.
   - One approach: prove a general lemma that for n ≥ 200 and m < n, we have n^m < 2^n, then use this to bound the polynomial terms.
   - Alternatively, use induction on n with a base case at n = 100*k + c + 100.

2. **Complete the pigeonhole principle step in `shannon_counting_argument`:** Once `poly_quadratic_bound` is complete, the final sorry in `shannon_counting_argument` can be addressed by formalizing the cardinality argument. This requires showing that if `|circuits| < |functions|`, then there exists a function not computed by any circuit of the given size.

## Blockers

- Formalizing polynomial vs exponential growth for arbitrary k in Lean's Nat requires careful arithmetic, but the threshold approach (n ≥ 100*k + c + 100) provides a clear path forward.
- Formalizing the pigeonhole principle for function spaces requires additional type-theoretic infrastructure, but the mathematical content is complete.

## Blockers

- Formalizing polynomial vs exponential growth in Lean's Nat requires careful arithmetic, but the threshold approach (n ≥ 100*k + c + 100) provides a clear path forward.
- Formalizing the pigeonhole principle for function spaces requires additional type-theoretic infrastructure, but the mathematical content is complete.

## Follow-up Work

After completing Task 7:
- Reassess the proof structure to ensure it correctly captures Shannon's counting argument.
- Verify that the statement of `shannon_counting_argument` is at the correct existential level (it shows that *some* Boolean functions require large circuits, not that SAT specifically does).
- Do not add stronger claims about SAT lower bounds without explicit proof.
