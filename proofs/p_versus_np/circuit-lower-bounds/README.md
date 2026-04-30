# Approach: Circuit Complexity Lower Bounds

**Priority:** 90

**Status:** Active — Task 6 complete; Task 7 in progress; `p_neq_np` compiles conditionally on two axioms; two `sorry`s remain in Task 7

**Relationship to the repository goal:** Main proof track. This approach directly targets `P ≠ NP` by formalizing the statement that sufficiently strong SAT circuit lower bounds would separate `P` from `NP`.

---

## Problem Statement

Prove that sufficiently strong Boolean circuit lower bounds for NP problems are enough to separate `P` from `NP`.
Specifically, formalize the argument that if an NP-complete problem such as SAT requires superpolynomial
circuit complexity, then `P ≠ NP`.

## Scope discipline

- Work in this folder must stay tied to the goal of settling P vs NP.
- Infrastructure results are useful only when they move this lower-bound route forward.
- Do not present Shannon-style counting progress as if it settled the SAT lower-bound problem itself.
- Keep the route barrier-aware.
- Counting lemmas and asymptotic bounds are worthwhile here only insofar as they clarify what this route can and cannot prove about explicit NP languages.

---

## Tasks

- [x] Task 1: Formalize Boolean circuit definitions (`BoolCircuit`, `Gate`, `CircuitNode`, `evalCircuit`)
- [x] Task 2: Define `IsPolynomial`, `inP`, and `inNP` in the circuit model
- [x] Task 3: Add sanity lemmas (`eval_const_true`, `eval_const_false`, `eval_var_zero`)
- [x] Task 4: Axiomatize Cook–Levin (`sat_is_np_complete`)
- [x] Task 5: Prove the conditional reduction from SAT circuit lower bounds to `P ≠ NP`
- [x] Task 6: Prove `circuit_count_lt_functions_at_n` — complete for all `n ≥ 4`
- [ ] Task 7: Complete `shannon_counting_argument` without overstating what it implies

---

## Key Axioms / Open Boundary

1. **`sat_is_np_complete`** — Cook–Levin theorem. Classically provable; formal proof is lengthy.
2. **`sat_has_superpoly_lower_bound`** — SAT requires superpolynomial-size circuits.
   **This is the unresolved step that would settle the P vs NP question in this route.**

The compiled `p_neq_np` theorem in `Proof.lean` is conditional on these assumptions.
Treat it as progress on the route, not as a solved proof of P vs NP.

---

## Immediate Next Steps

### Task 6 — COMPLETE

`circuit_count_lt_functions_at_n` compiles for all `n ≥ 4` without `sorry`. No further work needed.

### Task 7 — Complete `shannon_counting_argument` (two `sorry`s remain)

**Sorry 1: `poly_quadratic_bound_k_ge_1` — n ≥ 67108864 case (line 1259)**

The proof handles each power-of-2 range up to `n < 67108864` by explicit case splits. The branch `n ≥ 67108864` uses `sorry`.

Two viable approaches:
- **Extend the case split:** Add one more doubling step using the same pattern already established (bound `n < 134217728 = 2^27`, compute the matching `k` bound, apply `norm_num` and `omega`). This follows directly from the pattern at lines 1231–1252.
- **General lemma:** Prove `pow_lt_two_pow : ∀ m n, n ≥ 2*m + 10 → n^m < 2^n` by induction on `m`. Then replace all the case-split branches with a single application of this lemma. The base case `n^0 = 1 < 2^n` is trivial; the inductive step uses `n^(m+1) = n * n^m < n * 2^n ≤ 2^n * 2^n = 2^(2n) ≤ 2^(2^n)` together with exponential dominance.

**Sorry 2: Pigeonhole step in `shannon_counting_argument` (line 1815)**

Goal: `boolean_function_count n ≤ circuit_count_upper_bound n (p n)`.

Context: `h_all_computable` gives that every Boolean function has a circuit of size ≤ `p n`; `circuitForFunction` (defined nearby using `Classical.choose`) maps each function to such a circuit and its injectivity is already proven (see lines 1240–1258).

Recommended approach:
- Apply `Fintype.card_le_of_injective` with `circuitForFunction` as the injection.
- This requires `Fintype` instances for `(Fin n → Bool) → Bool` (the type of Boolean functions) and for the type of circuits bounded in size. The function type already has a `Fintype` instance in Mathlib. For the circuit bound, you may need to show the image lands in a `Finset` whose cardinality is `circuit_count_upper_bound n (p n)`.
- Alternatively, derive `boolean_function_count n ≤ circuit_count_upper_bound n (p n)` directly from the definitions using `Finset.card_le_card` on a suitable pair of finsets.

Keep the final statement honest: Shannon counting yields existential lower bounds for *some* Boolean functions, not a SAT-specific lower bound.

## Guidance for the next researcher pass

- Focus on `poly_quadratic_bound_k_ge_1` (Sorry 1) first; it is the most tractable remaining sorry.
- Once Task 7 compiles, stop and reassess before adding any stronger claim: the next missing ingredient would still be an explicit SAT lower bound, not more existential counting.
- Do not branch from this folder into quantum, proof-complexity, or GCT explorations unless the Project Leader creates a separate justified route.

---

## Library Code

Reusable definitions live in `lib/PVsNpLib/Utils.lean` and are imported via `import PVsNpLib`.
