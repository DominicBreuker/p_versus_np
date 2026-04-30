# Progress Notes

**Last Updated:** 2026-04-30 05:09:52 UTC (continued)

**Track role:** Main P vs NP proof track.

**Status:** Active — Fixed compilation errors in `poly_quadratic_bound` (k=0 case). Two `sorry`s remain in Task 7. File compiles cleanly.

---

## Current State

- The circuit model (`BoolCircuit`, `evalCircuit`, `inP`, `inNP`) is formalized.
- The proof file imports both `Mathlib` and `PVsNpLib`, so this track also serves as a technical example that shared imports work in proof files.
- `sat_is_np_complete` and `sat_has_superpoly_lower_bound` remain axioms.
- `sat_superpolynomial_implies_p_neq_np` and `p_neq_np` compile as **conditional** results.
- **Task 6 COMPLETED:** `circuit_count_lt_functions_at_n` now compiles for all `n ≥ 4` without `sorry`, using helper lemmas for polynomial vs exponential bounds.
- **Task 7 PROGRESS:** `shannon_counting_argument` structure is in place with `poly_quadratic_bound` significantly advanced.

## What Was Changed in This Session

### Files Modified
- `proofs/p_versus_np/circuit-lower-bounds/Proof.lean`:
  - **FIXED compilation errors in `poly_quadratic_bound` (k=0 case):**
    - Simplified the c > 95 branch to use `poly_quadratic_bound_k0` directly with threshold `2*c + 5 ≤ n`
    - Fixed the c = 0 case in the k ≥ 1 branch to handle the simplified goal `¬n = 0` after `simp`
    - Fixed type mismatch: changed `poly_quadratic_bound_k_ge_1` to prove `(c * n^k + c)^2 + ...` instead of `(c * n^k + c + c)^2 + ...` to match `poly_quadratic_bound`
  - Added detailed mathematical notes to both remaining `sorry` locations explaining the proof strategy and blockers

### Key Insights
- The k=0 case of `poly_quadratic_bound` is now **fully complete** with no sorries
- The compilation errors were caused by malformed `calc` blocks and type mismatches
- Both remaining sorries (`poly_quadratic_bound_k_ge_1` and the pigeonhole step) have clear mathematical content but require complex formalization in Lean's Nat arithmetic and type system

## Remaining Tasks

1. **Complete `poly_quadratic_bound_k_ge_1` (line 262):** Need to prove that for k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100, we have `(c * n^k + c)^2 + 3*(c * n^k + c) + 1 < 2^n`.
   - **Approach:** Use induction on n starting from n₀ = 100*k + c + 100
   - **Base case:** For n = n₀ ≥ 200, bound LHS by 4*c^2*n^(2k) + 6*c*n^k + 1 and show this < 2^n
   - **Inductive step:** Show LHS(n+1) < 2 * LHS(n) < 2 * 2^n = 2^(n+1) for n ≥ n₀
   - **Blocker:** Formalizing polynomial vs exponential growth for arbitrary k in Lean's Nat

2. **Complete the pigeonhole principle step in `shannon_counting_argument` (line 457):** Need to derive `False` from:
   - `h_all_computable`: ∀ f, ∃ c with circuitSize c ≤ p n, ∀ inp, evalCircuit c inp = f inp
   - `h_count`: circuit_count_upper_bound n (p n) < boolean_function_count n = 2^(2^n)
   - **Approach:** Use Fintype instances to formalize the cardinality argument
   - **Blocker:** The type `(Fin n → Bool) → Bool` doesn't have a Fintype instance in Lean, making cardinality arguments difficult

## Recommended Next Step

Focus on completing `poly_quadratic_bound_k_ge_1` first, as it is more tractable.

**Detailed approach for `poly_quadratic_bound_k_ge_1`:**
1. Prove a helper lemma: for n ≥ 200 and k ≥ 1, (m+1)^k ≤ 2 * m^k (holds for m ≥ k+1)
2. Use this to show LHS(m+1) < 2 * LHS(m) for m ≥ n₀
3. Combine with IH: LHS(m+1) < 2 * LHS(m) < 2 * 2^m = 2^(m+1)
4. For the base case at n₀, use the threshold to ensure n₀ is large enough that 2^n₀ dominates the polynomial

**Alternative approach:**
- Prove a general lemma `n_pow_m_lt_two_pow_n`: for n ≥ 2*m + 10 and m ≥ 1, n^m < 2^n
- Use this to bound n^(2k) < 2^n for n ≥ 2*(2k) + 10
- Since n ≥ 100*k + c + 100 ≥ 2*(2k) + 10, we have n^(2k) < 2^n
- Then bound LHS by a multiple of n^(2k) and use the exponential bound

**For the pigeonhole step:**
- The mathematical content is clear: if |A| < |B|, there cannot be a surjection from A to B
- Formalization requires Fintype infrastructure for function spaces
- Consider defining a finite representation of Boolean functions (e.g., as Fin (2^n) → Bool) and using existing Fintype lemmas

## Blockers

- Formalizing polynomial vs exponential growth for arbitrary k in Lean's Nat requires careful arithmetic with precise bounds
- Formalizing the pigeonhole principle for function spaces requires Fintype instances and cardinality infrastructure that doesn't exist for the type `(Fin n → Bool) → Bool`

## Follow-up Work

After completing Task 7:
- Reassess the proof structure to ensure it correctly captures Shannon's counting argument
- Verify that the statement of `shannon_counting_argument` is at the correct existential level (it shows that *some* Boolean functions require large circuits, not that SAT specifically does)
- Do not add stronger claims about SAT lower bounds without explicit proof
