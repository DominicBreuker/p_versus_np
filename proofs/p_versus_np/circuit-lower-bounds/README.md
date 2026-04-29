# Approach: Circuit Complexity Lower Bounds

**Priority:** 90

**Status:** Active — conditional P ≠ NP proof compiled; Shannon counting argument has two remaining `sorry` placeholders

---

## Problem Statement

Prove that Boolean circuit complexity lower bounds for NP problems are sufficient to separate P from NP.
Specifically, formalize the argument that if any NP-complete problem (e.g., SAT) requires superpolynomial
circuit complexity, then P ≠ NP.

**Approach:**
1. Define Boolean circuits and circuit complexity formally in Lean4. ✓
2. Define the complexity classes P and NP in terms of circuit families. ✓
3. Prove (or assume as axiom) that SAT is NP-complete. ✓ (axiomatized)
4. Develop lower bound lemmas showing exponential circuit complexity for some NP instance.
5. Conclude P ≠ NP. ✓ (conditional on steps 3–4)

---

## Tasks

- [x] Task 1: Formalize Boolean circuit definitions (BoolCircuit, Gate, CircuitNode, evalCircuit)
- [x] Task 2: Fix `evalCircuit` — implemented via foldl over topological node array
- [x] Task 3: Define `IsPolynomial` predicate and update `inP`
- [x] Task 4: Fix `inNP` witness encoding (combined 2*n bitstring, omega-verified index)
- [x] Task 5: Add sanity lemmas (`eval_const_true`, `eval_const_false`, `eval_var_zero`)
- [x] Task 6: Axiomatize Cook–Levin theorem (`sat_is_np_complete`)
- [x] Task 7: Prove `sat_superpolynomial_implies_p_neq_np` (no sorry — contradiction proof)
- [x] Task 8: State and prove `p_neq_np` (conditional on the two axioms below)
- [ ] Task 9: Prove `circuit_count_lt_functions_at_n` — remove sorry in the `n ≥ 9` branch
- [ ] Task 10: Complete `shannon_counting_argument` — remove both sorry placeholders

---

## Key Axioms (current proof relies on these)

1. **`sat_is_np_complete`** — Cook–Levin theorem. Classically provable; formal proof is
   laborious but not an open problem.
2. **`sat_has_superpoly_lower_bound`** — SAT requires superpolynomial-size circuits.
   **This is the P vs NP problem itself.** Do not claim it is proven.

The `p_neq_np` theorem compiles, but it is a *conditional* proof:
it reduces P ≠ NP to the assumption that SAT has no polynomial circuit family.
That assumption is exactly what remains to be resolved.

---

## Immediate Next Steps

### Task 9 — Prove `circuit_count_lt_functions_at_n` for n ≥ 9

Goal: `(n + 1)^(n + 1) * 2^n < 2^(2^n)` for `n ≥ 9` (small cases n=4..8 already use `decide`).

**Recommended three-step proof route:**

**Step 1 — auxiliary lemma A:** `n + 1 ≤ 2^n` for `n ≥ 1`, by induction.

**Step 2 — auxiliary lemma B:** `(n + 1)^(n + 1) ≤ 2^(n * (n + 1))` using lemma A and
`Nat.pow_le_pow_left`.

**Step 3 — auxiliary lemma C:** `n^2 + 2*n < 2^n` for `n ≥ 9`, by induction.
- Base `n = 9`: `81 + 18 = 99 < 512 = 2^9`. Use `norm_num` or `decide`.
- Inductive step: `(n+1)^2 + 2*(n+1) = n^2 + 2n + 2n + 3`. Use `n ≤ 2^n - 1` (from A)
  and the inductive hypothesis to close with `omega` or `linarith`.

**Final assembly:**
```lean
-- (n+1)^(n+1) * 2^n ≤ 2^(n*(n+1)) * 2^n = 2^(n^2 + 2*n + n) ≤ 2^(n^2 + 2*n + n)
-- But n^2 + 2*n < 2^n (lemma C), so 2^(n^2 + 2*n + n) < 2^(2^n + n) ≤ 2^(2^n + 2^n) = 2^(2^(n+1))
-- More directly: n^2 + 2*n < 2^n, so n*(n+1) + n = n^2 + 2*n < 2^n ≤ 2^n * 2^n = 2^(2*n) ≤ 2^(2^n)
```

Useful Mathlib lemmas:
```lean
Nat.pow_le_pow_left  -- a ≤ b → a^n ≤ b^n
Nat.pow_lt_pow_right -- 1 < b → n < m → b^n < b^m
Nat.pow_add          -- b^(m+n) = b^m * b^n
```

Use `omega` for linear arithmetic and `nlinarith` or `linarith` for combining inequalities.

### Task 10 — Complete `shannon_counting_argument`

Once Task 9 is done, the path for a general polynomial `p` with `p n ≤ c * n^k + c` is:
1. Show that for large enough `n₀`, `p n ≤ n^(k+1)` for all `n ≥ n₀`.
2. Extend `circuit_count_lt_functions_at_n` to `circuit_count_upper_bound n (n^(k+1)) < boolean_function_count n`.
3. Use `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` (Mathlib pigeonhole) to conclude.

---

## Hints

- The `sat_has_superpoly_lower_bound` axiom is the problem itself — do not confuse progress on
  the Shannon argument (which gives *existential* lower bounds) with proving the SAT lower bound.
- The Shannon argument shows most functions need large circuits; getting from "most" to "SAT specifically"
  requires the NP-completeness of SAT (Cook–Levin), which is already axiomatized.
- `omega` handles linear arithmetic; use `nlinarith` or `Nat.pow_lt_pow_right` for exponential bounds.

---

## Library Code

Reusable definitions live in `lib/utils.lean`. Currently available:
- `IsPolynomial` predicate
- `BoolFn` type alias
