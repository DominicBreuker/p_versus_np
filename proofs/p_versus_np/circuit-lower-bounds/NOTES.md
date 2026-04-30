# Progress Notes

**Last Updated:** 2026-04-30 09:16:46 UTC

**Track role:** Main P vs NP proof track.

**Status:** Active — Task 6 complete; Task 7 in progress with sorries remaining in `poly_quadratic_bound_k_ge_1` (2 sorries) and pigeonhole step (1 sorry). The `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` lemma compiles. `p_neq_np` theorem compiles conditionally on axioms.

---

## Current State

- The circuit model (`BoolCircuit`, `evalCircuit`, `inP`, `inNP`) is formalized.
- `sat_is_np_complete` and `sat_has_superpoly_lower_bound` remain axioms.
- `sat_superpolynomial_implies_p_neq_np` and `p_neq_np` compile as **conditional** results.
- **Task 6 COMPLETE:** `circuit_count_lt_functions_at_n` compiles for all `n ≥ 4` without `sorry`.
- **Task 7 IN PROGRESS:** `shannon_counting_argument` requires completing:
  - `poly_quadratic_bound_k_ge_1`: 2 sorries remain (base case and inductive step)
  - Pigeonhole principle: 1 sorry remains

## Remaining Tasks

### 1. Complete `poly_quadratic_bound_k_ge_1`
Need to prove: for k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100, we have `(c * n^k + c)^2 + 3*(c * n^k + c) + 1 < 2^n`.

**Status:** Proof simplified to use `sorry` after fixing compilation errors. The theorem statement remains but proof structure was removed due to complexity in formalizing n^(2k) < 2^n.

**Blocker:** Formalizing that n₀^(2k) < 2^n₀ for n₀ ≥ 100*k + c + 100 is non-trivial in Lean's Nat arithmetic. The mathematical intuition is clear (exponential grows faster than polynomial), but requires either:
- Using real logarithms (not directly available in Lean's Nat)
- Manual induction on k showing n^k grows slower than 2^n
- Adjusting the threshold (e.g., to n ≥ 100*k² + c + 100) to simplify the bound

**Next step:** Either complete the proof using Nat arithmetic lemmas about polynomial vs exponential growth, or adjust the threshold to make the inequality easier to prove.

### 2. Complete the pigeonhole principle in `shannon_counting_argument`
**Status:** The mathematical argument is complete. The `sorry` captures that we need Fintype instances for cardinality reasoning with function types `(Fin n → Bool) → Bool` and circuits.

**Blocker:** Mathlib doesn't provide Fintype instances for higher-order function types like `(Fin n → Bool) → Bool`. Options:
- Define an explicit bijection to `Fin (2^(2^n))` (encoding truth tables)
- Work with circuit enumeration directly instead of Fintype cardinality
- Define a auxiliary type with explicit Fintype instances

**Next step:** Choose an approach and implement the Fintype infrastructure, or reframe the argument to avoid needing Fintype instances.

---

## Summary of Changes

### Completed
- Fixed `four_n_squared_plus_six_n_plus_one_lt_two_pow_n` (proves 4*n² + 6*n + 1 < 2^n for n ≥ 196)
- Both k = 0 and k ≥ 1 cases of `poly_quadratic_bound` now compile
- `poly_quadratic_bound` relies on `poly_quadratic_bound_k0` for k = 0
- `p_neq_np` correctly uses `Axiom.sat_has_superpoly_lower_bound`

### Left as `sorry`
1. `poly_quadratic_bound_k_ge_1`: Requires n^(2k) < 2^n inequality
2. Inductive step of `poly_quadratic_bound_k_ge_1`
3. Pigeonhole argument in `shannon_counting_argument`

---

## Recommended Next Steps

1. **Priority 1:** Complete `poly_quadratic_bound_k_ge_1`. This is the main arithmetic blocker.
   - Try using `n^(2k) ≤ n^n` and showing n^n < 2^n (false for n > 2, so won't work)
   - Try n^(2k) < (2^n)^k and showing (2^n)^k < 2^n, which means k < 1 (contradicts k ≥ 1)
   - Consider using a higher threshold like n ≥ 200*k + c + 100 to make analysis easier

2. **Priority 2:** Complete pigeonhole argument
   - Explore using `exists_ne_map_eq_of_card_lt` or similar cardinality lemmas
   - Consider working with explicit truth table encodings as `Fin (2^(2^n))`

3. **Future work:** Once Task 7 is complete, verify the overall proof structure correctly captures Shannon's counting argument, noting that it proves existentially that *some* Boolean functions require large circuits, not explicitly for SAT.
