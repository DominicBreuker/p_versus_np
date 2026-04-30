# Project Overview

**Last Updated:** 2026-04-30 (project-leader review: Task 6 confirmed complete, Task 7 in progress, tighten next-step guidance)

---

## Goal

Solve the P vs NP problem in Lean4.

Any additional problem in `proofs/` is allowed only if it is a documented material step toward an existing P vs NP proof approach.

## Current Proof Tracks

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — Task 6 complete; Task 7 in progress with k=0 case proven; two `sorry`s remain (`poly_quadratic_bound_k_ge_1` and the pigeonhole step in `shannon_counting_argument`); `p_neq_np` compiles conditionally | Direct attack on `P ≠ NP`; the support track exists only to finish reusable circuit-model infrastructure |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 60 | Active — necessary support track; three `sorry`s remain: `liftCircuit_eval`, well-formedness in `p_subset_np`, and eval equivalences | Supports `p_versus_np/circuit-lower-bounds` by formalizing the easy inclusion `P ⊆ NP` and verifier lifting in the shared model |

## Progress Summary

- **Active proof tracks:** 2
- **Direct P vs NP tracks:** 1
- **Supporting subproblem tracks:** 1
- **Lean baseline:** `lake build` succeeds
- **Existing test baseline:** Python unit tests for the researcher workflow succeed
- **Proof files:** 2, and both still contain unresolved `sorry`s
- **Conditional separation theorem:** 1 (`p_neq_np`, dependent on two axioms; `shannon_counting_argument` also has sorries but is not on the critical path for `p_neq_np`)

## Assessment (2026-04-30)

### p_versus_np / circuit-lower-bounds (Priority 90)

- This remains the main repository attempt to settle `P ≠ NP`.
- **Task 6 is complete:** `circuit_count_lt_functions_at_n` compiles for all `n ≥ 4` without `sorry`.
- **Task 7 in progress:** `poly_quadratic_bound` k=0 case is fully proven. The k≥1 case (`poly_quadratic_bound_k_ge_1`, line 272) still has a `sorry`. The pigeonhole step in `shannon_counting_argument` (line 540) also still has a `sorry`.
- The `p_neq_np` theorem compiles as a conditional result dependent on two axioms: `sat_is_np_complete` and `sat_has_superpoly_lower_bound`.
- Note: `shannon_counting_argument` is infrastructure for existential counting lower bounds, not a proof that SAT specifically requires large circuits. The gap between existential counting and an explicit SAT lower bound is the core open barrier.
- The next target is `poly_quadratic_bound_k_ge_1`: prove that for k ≥ 1, c ≥ 1, and n ≥ 100*k + c + 100, we have `(c * n^k + c + c)^2 + 3*(c * n^k + c + c) + 1 < 2^n`. A general lemma `n^m < 2^n` for sufficiently large n is the key sublemma.

### p_subset_np / circuit-lifting (Priority 60)

- This track stays because it strengthens the same circuit-model foundation used by the main `p_versus_np` route.
- It is not a separate repository goal; it exists only to discharge standard verifier-lifting obligations once, cleanly, in the shared model.
- Three `sorry`s remain:
  1. `liftCircuit_eval`: needs an Array.foldl congruence lemma — if two functions agree on all elements of `arr`, then `arr.foldl push_f #[] = arr.foldl push_g #[]`. Consider inducting via `Array.foldl_toList` or `Array.induction_on`.
  2. Well-formedness for circuits from `inP` in `p_subset_np`: Var nodes with `idx ≥ n` already return `false` by the `evalNode` definition, so it may be possible to bypass the well-formedness requirement with a direct case split.
  3. Eval equivalences for both even and odd cases in `p_subset_np`: blocked by `liftCircuit_eval`.
- After `p_subset_np` compiles, this track should stop growing unless the main route needs a specific reusable lemma.

## Why no new route was added this run

- Both active tracks have concrete, identified next proof obligations.
- The repository is not in a stalled state; widening scope now would dilute researcher focus.
- The right leadership move is to sharpen guidance on the two open `sorry`s in Task 7 and the three `sorry`s in `p_subset_np`.

## Workspace Rules

- The Project Leader must keep `proofs/` focused on P vs NP.
- New problems require an explicit documented relationship to an existing P vs NP proof approach.
- Researchers should not drift into unrelated complexity theory or benchmark theorem proving.
