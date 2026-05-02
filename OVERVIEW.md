# Project Overview

**Last Updated:** 2026-04-30 (project-leader review: `evalNode_normalizeNodeCode` closed; 3 sorrys remain; guidance sharpened for all open obligations)

---

## Goal

Solve the P vs NP problem in Lean4.

Any additional problem in `proofs/` is allowed only if it is a documented material step toward an existing P vs NP proof approach.

## Current Proof Tracks

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](proofs/p_versus_np/) | [circuit_lower_bounds](proofs/p_versus_np/circuit_lower_bounds/) | 90 | Active — Task 6 complete; Task 7 in progress; **3 `sorry`s remain** (`evalCircuit_normalizeCircuit` line 389; `poly_quadratic_bound_k_ge_1` line 797; pigeonhole step line 1140) | Direct attack on `P ≠ NP`; the support track exists only to finish reusable circuit-model infrastructure |
| [p_subset_np](proofs/p_subset_np/) | [circuit_lifting](proofs/p_subset_np/circuit_lifting/) | 0 | ✅ Complete — `p_subset_np` proven; 0 `sorry`s; frozen | Supports `p_versus_np/circuit_lower_bounds`; supplies the easy inclusion `P ⊆ NP` in the shared model |

## Progress Summary

- **Active proof tracks:** 1 (direct P vs NP route)
- **Completed support tracks:** 1 (`p_subset_np/circuit_lifting`)
- **Direct P vs NP tracks:** 1
- **Lean baseline:** `lake env lean Proof.lean` succeeds
- **Proof files:** 2; `circuit_lower_bounds` has 3 unresolved `sorry`s; `circuit_lifting` has 0
- **Conditional separation theorem:** 1 (`p_neq_np`, dependent on two axioms)

## Assessment (2026-04-30)

### p_versus_np / circuit_lower_bounds (Priority 90)

- This remains the main repository attempt to settle `P ≠ NP`.
- **Task 6 is complete:** `circuit_count_lt_functions_at_n` compiles for all `n ≥ 4` without `sorry`.
- **Task 7 in progress:** Three `sorry`s remain:
  1. **`evalCircuit_normalizeCircuit` (line 389)** — bridge from the raw-circuit fold to the normalized fold. All sub-lemmas (`evalNode_normalizeNodeCode` ✅, `evalStep_fold_normalized_eq` ✅, `normalizeCircuit_nodes_list` ✅, `evalStep_fold_getElem?_preserve` ✅) are proven. Proof is an assembly task: split the normalized node list via `normalizeCircuit_nodes_list`, handle the `List.foldl_append` on the suffix of const-false padding nodes, and case-split on whether `c.output < c.nodes.size`.
  2. **`poly_quadratic_bound_k_ge_1` (line 797)** — the previous brittle case-split proof was removed for soundness; the whole body is currently `sorry`. Clean proof path: prove `pow_lt_two_pow_half (d n : Nat) (hn : n ≥ 4*d+10) : n^d < 2^(n/2)` by induction on `d`, then bound `(c*n^k+c)^2+3*(c*n^k+c)+1 ≤ 5*(c*n^k+c)^2 ≤ 5*n^(2k+2) < 5*2^(n/2) < 2^n` using `n ≥ 100*(k+1) ≥ 4*(2k+2)+10`.
  3. **Pigeonhole step in `shannon_counting_argument` (line 1140)** — goal is `boolean_function_count n ≤ circuit_count_upper_bound n (p n)`; use `Fintype.card_le_of_injective circuitForFunction h_inj` with the already-defined injection.
- The `p_neq_np` theorem compiles as a conditional result dependent on two axioms: `sat_is_np_complete` and `sat_has_superpoly_lower_bound`.
- **Important caveat:** Shannon counting yields existential lower bounds for *some* Boolean functions; it does not by itself establish a SAT-specific lower bound. The gap between `shannon_counting_argument` and an explicit SAT circuit lower bound is the core open barrier.

### p_subset_np / circuit_lifting (Priority 0) — COMPLETE

- **All `sorry`s resolved.** `p_subset_np` compiles with no axioms beyond the shared circuit model.
- This track is now frozen. No researcher time should be spent here unless the main route explicitly needs a shared lemma.

## Next Steps for Researchers

Focus exclusively on `proofs/p_versus_np/circuit_lower_bounds`:
1. **Priority 1:** `evalCircuit_normalizeCircuit` (line 389) — proof outline is in README; all sub-lemmas exist.
2. **Priority 2:** `poly_quadratic_bound_k_ge_1` (line 797) — prove `pow_lt_two_pow_half` helper by induction, then chain the bound; see README.
3. **Priority 3:** Pigeonhole step (line 1140) — apply `Fintype.card_le_of_injective`.

## Why no new route was added this run

- The main track has three concrete, identified next proof obligations.
- The support track is complete.
- The right leadership move is to sharpen guidance on the 3 open `sorry`s in Task 7 and close the most tractable one (`evalNode_normalizeNodeCode` ✅ done).

## Workspace Rules

- The Project Leader must keep `proofs/` focused on P vs NP.
- New problems require an explicit documented relationship to an existing P vs NP proof approach.
- Researchers should not drift into unrelated complexity theory or benchmark theorem proving.
