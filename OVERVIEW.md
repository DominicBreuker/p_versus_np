# Project Overview

**Last Updated:** 2026-04-29 (workflow migration to problem/approach proof layout)

---

## Goal

Build a structured Lean4 research workspace for major complexity-theory problems, with `P versus NP` as the flagship target.

## Current Proof Tracks

| Problem | Approach | Priority | Status |
|---------|----------|----------|--------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — conditional P ≠ NP proof exists; Shannon counting argument remains open |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 80 | Active — proof stub exists for a likely achievable foundational theorem |
| [deterministic_time_hierarchy_theorem](proofs/deterministic_time_hierarchy_theorem/) | [diagonalization](proofs/deterministic_time_hierarchy_theorem/diagonalization/) | 70 | Active — monotonicity proven; diagonalization remains blocked |

## Progress Summary

- **Active proof tracks:** 3
- **Stalled proof tracks:** 0
- **Dead ends:** 0
- **Unconditional proofs completed:** 0
- **Conditional proofs:** 1 (`p_neq_np` in `proofs/p_versus_np/circuit-lower-bounds`, still assumes open lower-bound axioms)

## Assessment (2026-04-29)

### p_versus_np / circuit-lower-bounds

- The conditional `p_neq_np` proof compiles.
- The blocking subproblem is the Shannon counting argument.
- This is exactly the kind of difficult derived problem that may deserve its own future `proofs/<problem>/...` folder if it becomes a sustained research target.

### p_subset_np / circuit-lifting

- The target is a concrete theorem rather than an open problem.
- The main open work is the `liftCircuit_eval` lemma and the resulting verifier proof.
- This is a strong candidate for the next sorry-free theorem in the repository.

### deterministic_time_hierarchy_theorem / diagonalization

- `inDTIME_mono` and `inDTIME_congr` are proven.
- The remaining work is concentrated in encoding, universal simulation packaging, and the diagonal contradiction.

## Workflow Notes

- The Project Leader now maintains `proofs/README.md`, each `proofs/<problem>/README.md`, and `references/README.md`.
- Researchers operate only inside one `proofs/<problem>/<approach>/` target per run.
- Researcher target selection is randomized with probability proportional to the numeric priority recorded in `proofs/README.md`.
