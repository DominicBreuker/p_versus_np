# Progress Notes

**Last Updated:** 2026-04-30 05:09:52 UTC (continued)

**Track role:** Main P vs NP proof track.

**Status:** Active — Fixed compilation errors in `poly_quadratic_bound` (k=0 case). Moved `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` lemma before `poly_quadratic_bound_k_ge_1`. Three `sorry`s remain (2 in `poly_quadratic_bound_k_ge_1`, 1 in pigeonhole step). File compiles cleanly.

---

## Current State

- The circuit model (`BoolCircuit`, `evalCircuit`, `inP`, `inNP`) is formalized.
- The proof file imports both `Mathlib` and `PVsNpLib`, so this track also serves as a technical example that shared imports work in proof files.
- `sat_is_np_complete` and `sat_has_superpoly_lower_bound` remain axioms.
- `sat_superpolynomial_implies_p_neq_np` and `p_neq_np` compile as **conditional** results.
- **Task 6 COMPLETED:** `circuit_count_lt_functions_at_n` now compiles for all `n ≥ 4` without `sorry`, using helper lemmas for polynomial vs exponential bounds.
- **Task 7 PROGRESS:** `shannon_counting_argument` structure is in place with `poly_quadratic_bound` significantly advanced. `poly_quadratic_bound_k_ge_1` has proof structure in place with base case and inductive step identified.

## What Was Changed in This Session

### Files Modified
- `proofs/p_versus_np/circuit-lower-bounds/Proof.lean`:
  - **FIXED compilation errors in `poly_quadratic_bound` (k=0 case):**
    - Simplified the c > 95 branch to use `poly_quadratic_bound_k0` directly with threshold `2*c + 5 ≤ n`
    - Fixed the c = 0 case in the k ≥ 1 branch to handle the simplified goal `¬n = 0` after `simp`
    - Fixed type mismatch: changed `poly_quadratic_bound_k_ge_1` to prove `(c * n^k + c)^2 + ...` instead of `(c * n^k + c + c)^2 + ...` to match `poly_quadratic_bound`
  - **MOVED** `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` lemma before `poly_quadratic_bound_k_ge_1` so it can be used in the proof
  - **ADDED** proof structure for `poly_quadratic_bound_k_ge_1`:
    - Set up induction on n using `Nat.le_induction` with base case at n₀ = 100*k + c + 100
    - Proved LHS bound: `(c * n₀^k + c)^2 + 3*(c * n₀^k + c) + 1 ≤ (4*c^2 + 6*c + 1) * n₀^(2k)`
    - Proved polynomial part: `4*c^2 + 6*c + 1 < 2^n₀` using `four_n_squared_plus_six_n_plus_one_lt_two_pow_n`
    - Identified remaining gap: need to prove `n₀^(2k) < 2^n₀` for n₀ ≥ 100*k + c + 100
  - Added detailed mathematical notes to both remaining `sorry` locations explaining the proof strategy and blockers

### Key Insights
- The k=0 case of `poly_quadratic_bound` is now **fully complete** with no sorries
- The compilation errors were caused by malformed `calc` blocks and type mismatches
- The `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` lemma is now available for use in `poly_quadratic_bound_k_ge_1`
- The base case of `poly_quadratic_bound_k_ge_1` reduces to proving `n₀^(2k) < 2^n₀` for n₀ ≥ 100*k + c + 100
- Mathematical analysis shows the inequality holds for practical values but requires careful formalization

## Remaining Tasks

1. **Complete `poly_quadratic_bound_k_ge_1` (line ~300):** Need to prove that for k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100, we have `(c * n^k + c)^2 + 3*(c * n^k + c) + 1 < 2^n`.
   - **Status:** Proof structure in place with base case and inductive step. Polynomial part proven. Need to prove `n₀^(2k) < 2^n₀` for the base case and complete the inductive step.
   - **Approach for base case:** Use the threshold n₀ ≥ 100*k + c + 100 to show 2k * log2(n₀) < n₀ (mathematically true for all k ≥ 1, n₀ ≥ 200)
   - **Approach for inductive step:** Show LHS(m+1) < 2 * LHS(m) for m ≥ n₀, then combine with IH
   - **Blocker:** Formalizing the inequality `n₀^(2k) < 2^n₀` in Lean's Nat arithmetic without real logarithms

2. **Complete the pigeonhole principle step in `shannon_counting_argument` (line ~629):** Need to derive `False` from:
   - `h_all_computable`: ∀ f, ∃ c with circuitSize c ≤ p n, ∀ inp, evalCircuit c inp = f inp
   - `h_count`: circuit_count_upper_bound n (p n) < boolean_function_count n = 2^(2^n)
   - **Approach:** Use Fintype instances to formalize the cardinality argument
   - **Blocker:** The type `(Fin n → Bool) → Bool` doesn't have a Fintype instance in Lean, making cardinality arguments difficult

## Recommended Next Step

Focus on completing `poly_quadratic_bound_k_ge_1` first, as it is more tractable.

**Detailed approach for `poly_quadratic_bound_k_ge_1`:**
1. **Base case:** Prove `n₀^(2k) < 2^n₀` for n₀ = 100*k + c + 100
   - Use induction on n starting from n₀
   - For the base case at n₀, use the fact that n₀ ≥ 200 and 2k ≤ n₀
   - Key insight: For n₀ ≥ 200, we have (n₀ - 101)/50 * log2(n₀) + 3 < n₀, which implies n₀^((n₀-101)/50) < 2^n₀ / 8
   - Since 2k ≤ (n₀ - 101)/50, we have n₀^(2k) ≤ n₀^((n₀-101)/50) < 2^n₀ / 8
2. **Inductive step:** Show LHS(m+1) < 2 * LHS(m) for m ≥ n₀
   - Prove helper lemma: for m ≥ 2*k, (m+1)^k ≤ (1 + 1/m)^k * m^k < 2 * m^k (since (1+1/m)^k < 2 for m ≥ k)
   - Use this to show c*(m+1)^k + c < 2*(c*m^k + c)
   - Then LHS(m+1) < 2^2 * LHS(m) = 4 * LHS(m), but we need < 2 * LHS(m)
   - Alternative: Show (c*(m+1)^k + c)^2 < 2 * (c*m^k + c)^2 and 3*(c*(m+1)^k + c) < 2 * 3*(c*m^k + c)

**Alternative approach for base case:**
- Prove directly that (4*c^2 + 6*c + 1) * n₀^(2k) < 2^n₀
- Use: 4*c^2 + 6*c + 1 < 2^n₀ (already proven) and n₀^(2k) < 2^n₀ / (4*c^2 + 6*c + 1)
- The second inequality is equivalent to 2k * log2(n₀) + log2(4*c^2 + 6*c + 1) < n₀
- With n₀ = 100*k + c + 100 and c ≤ n₀, this holds mathematically

**For the pigeonhole step:**
- The mathematical content is clear: if |A| < |B|, there cannot be a surjection from A to B
- Formalization requires Fintype infrastructure for function spaces
- Consider defining a finite representation of Boolean functions (e.g., as Fin (2^n) → Bool) and using existing Fintype lemmas

## Blockers

- Formalizing polynomial vs exponential growth for arbitrary k in Lean's Nat requires careful arithmetic with precise bounds. The threshold n ≥ 100*k + c + 100 may need to be increased to n ≥ 100*k^2 + c + 100 or similar for a cleaner proof.
- Formalizing the pigeonhole principle for function spaces requires Fintype instances and cardinality infrastructure that doesn't exist for the type `(Fin n → Bool) → Bool`

## Follow-up Work

After completing Task 7:
- Reassess the proof structure to ensure it correctly captures Shannon's counting argument
- Verify that the statement of `shannon_counting_argument` is at the correct existential level (it shows that *some* Boolean functions require large circuits, not that SAT specifically does)
- Do not add stronger claims about SAT lower bounds without explicit proof
