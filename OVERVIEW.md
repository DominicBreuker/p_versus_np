# Project Overview

**Last Updated:** 2026-04-29 (project-leader review: keep the current 2-track plan and tighten scope)

---

## Goal

Solve the P vs NP problem in Lean4.

Any additional problem in `proofs/` is allowed only if it is a documented material step toward an existing P vs NP proof approach.

## Current Proof Tracks

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — direct but still highly incomplete route to `P ≠ NP`; current Lean progress is a conditional reduction plus partial counting infrastructure | Direct attack on `P ≠ NP`; the support track exists only to finish reusable circuit-model infrastructure |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 60 | Active — necessary support track; remaining work is routine Lean proof engineering in the same circuit model | Supports `p_versus_np/circuit-lower-bounds` by formalizing the easy inclusion `P ⊆ NP` and verifier lifting in the shared model |

## Progress Summary

- **Active proof tracks:** 2
- **Direct P vs NP tracks:** 1
- **Supporting subproblem tracks:** 1
- **Lean baseline:** `lake build` succeeds
- **Existing test baseline:** Python unit tests for the researcher workflow succeed
- **Proof files:** 2, and both still contain unresolved `sorry`s
- **Conditional separation theorem:** 1 (`p_neq_np`, still dependent on axioms plus unfinished counting lemmas)

## Assessment (2026-04-29)

### p_versus_np / circuit-lower-bounds (Priority 90)

- This remains the main repository attempt to settle `P ≠ NP`.
- The formalization already captures the conditional reduction from sufficiently strong SAT circuit lower bounds to `P ≠ NP`.
- Current progress is still infrastructure only: Shannon counting is incomplete and, even when finished, gives existential lower bounds rather than an explicit SAT lower bound.
- The next substantive target is still the arithmetic lemma `circuit_count_lt_functions_at_n` for `n ≥ 9`, followed by an honest statement of the existential counting theorem.
- This track should stay narrow and barrier-aware; it should not expand into unrelated lower-bound programs unless they become concrete follow-on work for this exact route.

### p_subset_np / circuit-lifting (Priority 60)

- This track stays because it strengthens the same circuit-model foundation used by the main `p_versus_np` route.
- It is not a separate repository goal; it exists only to discharge standard verifier-lifting obligations once, cleanly, in the shared model.
- Remaining work is ordinary Lean bookkeeping around `liftCircuit_eval`, `verifier_iff`, the even-size alignment in the verifier family, and the final assembly of `p_subset_np`.
- After `p_subset_np` compiles, this track should stop growing unless the main route needs a specific reusable lemma.

## Why no new route was added this run

- The repository already has concrete next steps on both active tracks, so the workspace is not in an “all tracks stalled” state.
- Adding a speculative third route now would widen the search space without producing a stronger near-term Lean milestone.
- The right leadership move for this run is therefore to sharpen guidance and keep researchers concentrated on the existing circuit-model program.

## Workspace Rules

- The Project Leader must keep `proofs/` focused on P vs NP.
- New problems require an explicit documented relationship to an existing P vs NP proof approach.
- Researchers should not drift into unrelated complexity theory or benchmark theorem proving.
