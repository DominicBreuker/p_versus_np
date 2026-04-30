# Approach: Circuit Complexity Lower Bounds

**Priority:** 90

**Status:** Active — Task 6 complete; Task 7 in progress; `p_neq_np` compiles conditionally on two axioms; **three `sorry`s remain** in Task 7

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

### Task 7 — Complete `shannon_counting_argument` (three `sorry`s remain)

**Sorry 1 (CLOSED ✅): `evalNode_normalizeNodeCode` (line 303, 2026-04-30)**

Proved by Project Leader run 2026-04-30. Proof pattern: `rcases`/`cases gate` + case splits for each constructor; `Not [child]` branch uses `split_ifs` + `simp [Array.getD, h_not_lt]`; `And`/`Or` branches use `rw [foldl_*_map_val, foldl_*_map_eval, ← *_fold_preserved]`.

**Sorry 2 (OPEN): `evalCircuit_normalizeCircuit` (line 389)**

Goal: `evalCircuit (normalizedToRaw (normalizeCircuit c hsize)) inp = evalCircuit c inp`.

All required pieces are already proven:
- `evalNode_normalizeNodeCode` (✅ now closed)
- `evalStep_fold_normalized_eq` (✅ uses `evalNode_normalizeNodeCode`)
- `evalStep_fold_getElem?_preserve`
- `normalizeCircuit_nodes_list`

Recommended proof outline:
1. Unfold `evalCircuit` / `normalizedToRaw` on both sides.
2. Convert `Array.foldl` to `List.foldl` via `Array.foldl_toList` or `Array.toList_ofFn`.
3. Use `normalizeCircuit_nodes_list` to split the normalized node list into the original-size prefix and a `List.replicate (s - c.nodes.size) (NodeCode.const false)` suffix.
4. Apply `List.foldl_append` to split the fold.
5. The prefix fold: apply `evalStep_fold_normalized_eq` (requires `#[].size + c.nodes.size ≤ s`, i.e., `hsize`).
6. The suffix fold: each `nodeCodeToRaw (.const false)` evaluates to `false`; show the suffix fold just appends `false` values (does not change earlier positions).
7. Output: case-split on `c.output < c.nodes.size`. If true, use `evalStep_fold_getElem?_preserve`. If false, both sides return `false`.

**Sorry 3 (OPEN): `poly_quadratic_bound_k_ge_1` (line 797)**

Goal: For `k ≥ 1, c ≥ 1, n ≥ 100*k + c + 100`: `(c * n^k + c)^2 + 3*(c*n^k + c) + 1 < 2^n`.

The theorem body is currently a single `sorry` — the previous partial proof was removed for soundness. Proof strategy:

**Step A.** Prove a helper `pow_lt_two_pow_half`:
```
private theorem pow_lt_two_pow_half (d n : Nat) (hn : n ≥ 4 * d + 10) : n ^ d < 2 ^ (n / 2)
```
Proof by induction on `d`:
- Base `d = 0`: `1 < 2^(n/2)` since `n ≥ 10` gives `n/2 ≥ 5`, `2^5 = 32 > 1`.
- Step `d → d+1` (`n ≥ 4*(d+1)+10 = 4d+14`):
  - By IH: `n^d < 2^(n/2)` (since `n ≥ 4d+14 ≥ 4d+10`).
  - Have `n < 2^(n/2)` for `n ≥ 6` (and `n ≥ 14 ≥ 6`): prove this separately by induction (`Nat.lt_two_pow_self` and `Nat.lt_pow_self`).
  - Conclude: `n^(d+1) = n * n^d < 2^(n/2) * 2^(n/2) = 2^(2*(n/2)) ≤ 2^n`.

**Step B.** Bound the LHS of `poly_quadratic_bound_k_ge_1`:
- `c * n^k + c ≤ n * n^k = n^(k+1)` (since `c ≤ n - 100 ≤ n`).
- `M := c * n^k + c ≤ n^(k+1)`, so `M^2 + 3*M + 1 ≤ 5*M^2 ≤ 5*n^(2k+2)`.

**Step C.** Apply `pow_lt_two_pow_half` with `d = 2k+2`:
- `n ≥ 100*k + c + 100 ≥ 100*(k+1) ≥ 4*(2k+2) + 10 = 8k+18` (holds for all `k ≥ 0`).
- So `n^(2k+2) < 2^(n/2)`.

**Step D.** Combine: `5 * n^(2k+2) < 5 * 2^(n/2) < 2^n` (since `5 < 2^3 ≤ 2^(n/2)` for `n ≥ 6`). Chain: `(c*n^k+c)^2 + 3*(c*n^k+c) + 1 ≤ 5*n^(2k+2) < 2^n`.

**Sorry 4 (OPEN): Pigeonhole step in `shannon_counting_argument` (line 1140)**

Goal: `boolean_function_count n ≤ circuit_count_upper_bound n (p n)`.

Context: `h_all_computable` states every Boolean function has a circuit of size ≤ `p n`. An injective map `circuitForFunction` is defined nearby using `Classical.choose`, mapping each Boolean function to a circuit that computes it.

Recommended approach:
- Use `Fintype.card_le_of_injective circuitForFunction h_inj` where `h_inj` is the injectivity proof for `circuitForFunction`.
- This requires a `Fintype` instance for the type of normalized circuits with size ≤ `p n`. Such a `Fintype` instance follows from `NormalizedCircuit` being a finite type (already established via `Fintype (NormalizedCircuit n s)`).
- The cardinality bound on the target type gives `circuit_count_upper_bound n (p n)`.

## Guidance for the next researcher pass

- **Priority 1:** Prove `evalCircuit_normalizeCircuit` (Sorry 2) — the outline above is complete; all sub-lemmas exist.
- **Priority 2:** Prove `poly_quadratic_bound_k_ge_1` (Sorry 3) — prove `pow_lt_two_pow_half` first, then chain the bound.
- **Priority 3:** Prove the pigeonhole step (Sorry 4) using `Fintype.card_le_of_injective`.
- Once Task 7 compiles, stop and reassess before adding any stronger claim: the next missing ingredient would still be an explicit SAT lower bound, not more existential counting.
- Do not branch from this folder into quantum, proof-complexity, or GCT explorations unless the Project Leader creates a separate justified route.

---

## Library Code

Reusable definitions live in `lib/PVsNpLib/Utils.lean` and are imported via `import PVsNpLib`.
