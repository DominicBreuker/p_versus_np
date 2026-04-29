# Project Overview

**Last Updated:** 2026-04-29 (Project Leader review — all three original tracks assessed; new track added)

---

## Goal

Build a structured Lean4 research workspace for major complexity-theory problems, with `P versus NP` as the flagship target.

## Current Proof Tracks

| Problem | Approach | Priority | Status |
|---------|----------|----------|--------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — conditional P ≠ NP proof compiled; Shannon counting argument has two sorry |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 85 | Active — `liftCircuit` and `poly_half` proven; `liftCircuit_eval` and `verifier_iff` sorry |
| [deterministic_time_hierarchy_theorem](proofs/deterministic_time_hierarchy_theorem/) | [diagonalization](proofs/deterministic_time_hierarchy_theorem/diagonalization/) | 70 | Active — monotonicity proven; diagonalization pending |
| [p_closure_under_complement](proofs/p_closure_under_complement/) | [circuit_negation](proofs/p_closure_under_complement/circuit_negation/) | 50 | New — sorry-free proof should be achievable |

## Progress Summary

- **Active proof tracks:** 4
- **Stalled proof tracks:** 0
- **Dead ends:** 0
- **Unconditional sorry-free theorems:** 3 (`inDTIME_mono`, `inDTIME_congr`, `poly_half`)
- **Conditional proofs:** 1 (`p_neq_np` — assumes `sat_has_superpoly_lower_bound` and `sat_is_np_complete`)
- **Remaining `sorry` count:** ~5 across all tracks

## Assessment (2026-04-29)

### p_versus_np / circuit-lower-bounds (Priority 90)

- The conditional `p_neq_np` theorem compiles cleanly.
- The blocking sub-task is `circuit_count_lt_functions_at_n` for `n ≥ 9`.
- Recommended approach: three auxiliary lemmas (`n+1 ≤ 2^n`, power-tower bound, `n²+2n < 2^n`)
  all provable by induction; then the general `shannon_counting_argument` can follow.
- See `circuit-lower-bounds/README.md` for the detailed proof sketches.

### p_subset_np / circuit-lifting (Priority 85, promoted from 80)

- `liftCircuit` (type coercion) and `poly_half` (polynomial bound for m/2) are proven.
- The remaining `sorry` are both dependent-type bookkeeping, not open mathematics:
  1. `liftCircuit_eval`: show folding over the same node array with two extensionally equal
     input functions gives the same result. Strategy: prove node-by-node then lift by array induction.
  2. `verifier_iff`: show `L ((2*n)/2) f ↔ L n inp`. Reduce to `2*n/2 = n` then `funext + Fin.ext`.
- This is the **top priority sorry-free target** in the repository.

### deterministic_time_hierarchy_theorem / diagonalization (Priority 70)

- Tasks 1–6 complete and sorry-free (`inDTIME_mono`, `inDTIME_congr`, `encode_length`).
- Tasks 7–10 (diagonal language + membership proofs) are the remaining work.
- The `universal` decider is axiomatized via `universal_simulation`; use it as a black box.
- See `diagonalization/README.md` for the diagonal language construction strategy.

### p_closure_under_complement / circuit_negation (Priority 50, NEW)

- New track added this review cycle.
- Goal: prove `p_closed_under_complement` sorry-free.
- Key lemma: `negateCircuit_eval` — add a NOT gate at the output and show it flips the bit.
- All ingredients (`Array.foldl_push`, `Array.getD_push_eq`) are standard Lean4 array lemmas.
- This should be the easiest sorry-free proof in the repository.

## Workflow Notes

- The Project Leader maintains `proofs/README.md`, each `proofs/<problem>/README.md`, and `references/README.md`.
- Researchers operate only inside one `proofs/<problem>/<approach>/` target per run.
- Researcher target selection is randomized with probability proportional to the numeric priority in `proofs/README.md`.
