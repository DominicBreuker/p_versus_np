# Approach: Circuit Lifting for P ⊆ NP

**Priority:** 60

**Status:** ✅ COMPLETE — `p_subset_np` proven; 0 `sorry`s in `Proof.lean`

**Relationship to the repository goal:** This track supports `proofs/p_versus_np/circuit_lower_bounds` by proving the easy inclusion `P ⊆ NP` inside the same circuit model.

---

## Problem Statement

Formally prove

```lean
theorem p_subset_np {L : Language} (hL : inP L) : inNP L
```

using the circuit-model definitions already aligned with the main `p_versus_np` track.

## Why This Track Exists

- It strengthens the exact formal framework used by the main P vs NP route.
- It is standard mathematics / proof engineering, not an unrelated open problem.
- It gives a concrete way to exercise imports from both `Mathlib` and `PVsNpLib` in a proof file.
- Now that `p_subset_np` is proven, this folder should not grow further unless the main route needs a specific reusable lemma from it.

---

## Current State of `Proof.lean`

| Lemma/Theorem | Status |
|---|---|
| `liftCircuit` | ✓ defined |
| `liftCircuit_size` | ✓ proven |
| `poly_half` | ✓ proven |
| `liftCircuit_eval` | ✓ proven |
| `verifier_iff` | ✓ proven |
| `p_subset_np` | ✓ proven |
| `sanitizeCircuit` + lemmas | ✓ proven |

---

## Tasks

- [x] Task 1: Reuse the circuit-model definitions needed for this track
- [x] Task 2: Define `liftCircuit`
- [x] Task 3: Prove `liftCircuit_size`
- [x] Task 4: Prove `poly_half`
- [x] Task 5: Prove `liftCircuit_eval`
- [x] Task 6: Prove `verifier_iff`
- [x] Task 7: Complete `p_subset_np`

---

## How It Was Completed

The key insight was circuit sanitization:

- Added `sanitizeGate`, `sanitizeNode`, and `sanitizeCircuit` to rewrite any out-of-bounds `Gate.Var idx` to `Gate.Const false`.
- This preserves semantics for `BoolCircuit n` because `evalNode` already returns `false` when `idx ≥ n`.
- Proved `evalNode_sanitizeNode`, `sanitizeCircuit_size`, `sanitizeCircuit_wf`, and `evalCircuit_sanitizeCircuit`.
- In both the even and odd size branches of `p_subset_np`, lifted `sanitizeCircuit c` instead of the raw circuit `c`.

---

## Next Steps

This track is frozen. No further work is needed unless the main `p_versus_np/circuit_lower_bounds` route requires a specific reusable lemma from it.

If the sanitization lemmas become shared infrastructure, consider moving them into `lib/` in a separate cleanup task.
