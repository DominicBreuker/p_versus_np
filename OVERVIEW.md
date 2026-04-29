# Project Overview

**Last Updated:** 2026-04-29 (repository refocused on the sole goal of solving P vs NP)

---

## Goal

Solve the P vs NP problem in Lean4.

Any additional problem in `proofs/` is allowed only if it is a documented material step toward an existing P vs NP proof approach.

## Current Proof Tracks

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — main route toward a Lean proof of `P ≠ NP`; current work is still on the counting-argument infrastructure | Main proof track |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 60 | Active — supporting track; standard formalization work remains in the shared circuit model | Supports `p_versus_np/circuit-lower-bounds` by formalizing the easy inclusion `P ⊆ NP` in the same model |

## Progress Summary

- **Active proof tracks:** 2
- **Primary P vs NP tracks:** 1
- **Supporting subproblem tracks:** 1
- **Tracks removed as unrelated:** 2
- **Conditional separation proofs:** 1 (`p_neq_np`, still conditional on the open lower-bound assumption)
- **Proof files demonstrating imports:** 2 (`proofs/p_versus_np/circuit-lower-bounds/Proof.lean`, `proofs/p_subset_np/circuit-lifting/Proof.lean`)

## Assessment (2026-04-29)

### p_versus_np / circuit-lower-bounds (Priority 90)

- This remains the main repository attempt to settle `P ≠ NP`.
- The formalization already captures the conditional reduction from superpolynomial SAT circuit lower bounds to `P ≠ NP`.
- The open work is still the actual lower-bound route: the Shannon counting infrastructure is incomplete and does **not** solve P vs NP yet.
- The next substantive target is the arithmetic lemma `circuit_count_lt_functions_at_n` for `n ≥ 9`.

### p_subset_np / circuit-lifting (Priority 60)

- This track stays because it strengthens the same circuit-model foundation used by the main `p_versus_np` route.
- It is not a separate repository goal; it is a supporting formalization task.
- Remaining work is ordinary Lean bookkeeping around `liftCircuit_eval`, `verifier_iff`, and the final assembly of `p_subset_np`.

## Workspace Rules

- The Project Leader must keep `proofs/` focused on P vs NP.
- New problems require an explicit documented relationship to an existing P vs NP proof approach.
- Researchers should not drift into unrelated complexity theory or benchmark theorem proving.
