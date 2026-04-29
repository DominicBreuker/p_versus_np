# Approach: Circuit Lifting for P ⊆ NP

**Priority:** 60

**Status:** Active — supporting track with ordinary Lean proof obligations remaining; this should be finished, not expanded

**Relationship to the repository goal:** This track supports `proofs/p_versus_np/circuit-lower-bounds` by proving the easy inclusion `P ⊆ NP` inside the same circuit model.

---

## Problem Statement

Formally prove

```lean
theorem p_subset_np {L : Language} (hL : inP L) : inNP L
```

using the circuit-model definitions already aligned with the main `p_versus_np` track.

## Why This Track Still Exists

- It strengthens the exact formal framework used by the main P vs NP route.
- It is standard mathematics / proof engineering, not an unrelated open problem.
- It gives a concrete way to exercise imports from both `Mathlib` and `PVsNpLib` in a proof file.
- It should not grow into a second complexity-theory program once `p_subset_np` is finished.

---

## Current State of `Proof.lean`

| Lemma/Theorem | Status |
|---|---|
| `liftCircuit` | ✓ defined |
| `liftCircuit_size` | ✓ proven |
| `poly_half` | ✓ proven |
| `liftCircuit_eval` | ✗ sorry |
| `verifier_iff` | ✗ sorry |
| `p_subset_np` | ✗ sorry |

---

## Tasks

- [x] Task 1: Reuse the circuit-model definitions needed for this track
- [x] Task 2: Define `liftCircuit`
- [x] Task 3: Prove `liftCircuit_size`
- [x] Task 4: Prove `poly_half`
- [ ] Task 5: Prove `liftCircuit_eval`
- [ ] Task 6: Prove `verifier_iff`
- [ ] Task 7: Complete `p_subset_np`

---

## Immediate Next Steps

### Task 5 — Prove `liftCircuit_eval`

Show that the lifted circuit reads only the first `n` bits of a `Fin (2*n) → Bool` input.
The key work is dependent-type bookkeeping around `Fin.ext` and an induction over the shared node array.

### Task 6 — Prove `verifier_iff`

Reduce `((2 * n) / 2)` to `n`, then prove that the combined input restricted to its first half is propositionally equal to `inp`.

### Task 7 — Finish `p_subset_np`

Keep the final theorem specialized to the existing circuit model. Do not introduce a second verifier representation or extra abstraction layers unless they are needed to close the current proof.
The current blocker is the verifier-family size alignment.

---

## Hints

- Use `import Mathlib` explicitly for arithmetic and tactic support.
- Use `import PVsNpLib` for the shared `IsPolynomial` definition.
- The witness in the NP statement can be ignored; the verifier only needs the first half of the combined input.
- Handle the size mismatch in `p_subset_np` directly: the verifier only needs to be well-behaved on inputs of size `2 * n`, so solve that alignment before adding more helper infrastructure.
