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

### Task 5 — Prove `liftCircuit_eval` (line 119)

**Blocker:** Array.foldl congruence.

The `h_nodes` helper lemma is already proven: for all `i < c.nodes.size` and all `acc : Array Bool`,
`evalNode inp acc c.nodes[i]! = evalNode (fun i => inp ⟨i.val, _⟩) acc c.nodes[i]!`.

The remaining step is to lift this per-node equality to an equality of the full foldl results.

Recommended approach:
1. Convert the foldl to a list fold: `Array.foldl_toList` or `Array.foldl_eq_foldl_toList` to rewrite `c.nodes.foldl f #[]` as `c.nodes.toList.foldl f #[]`.
2. Induct on `c.nodes.toList`, using `h_nodes` at each index to justify that `f acc node = g acc node` and therefore the foldl states agree at every step.
3. Conclude by the equality of the final arrays (same output index, same values).

### Task 6 — Prove `verifier_iff` (line 191)

**Status: likely already compiles.** The theorem has a proof attempt using `Eq.rec` and `Fin.cast`. Check with `lean_diagnostic_messages` before attempting further changes.

### Task 7 — Finish `p_subset_np` (line 258)

Three sub-goals remain:

1. **Well-formedness (line 288):** Circuits from `inP` decode Var nodes as `idx < n`; Var nodes with `idx ≥ n` return `false` anyway by `evalNode`. Try removing the `IsWellFormed` assumption from `liftCircuit_eval` entirely and proving the result unconditionally using the same `h_nodes` argument (the `idx ≥ n` branch is unreachable because `evalNode` returns `false` for it on both sides).

2. **Even case eval equivalence (line 292):** Once `liftCircuit_eval` is proven unconditionally, this goal reduces to `hc_correct` on the restriction of `inp`.

3. **Odd case eval equivalence (line 315):** Prove a version of `liftCircuit_eval` for `liftCircuitTo`; the proof is identical (same node array, different phantom type).

---

## Hints

- Use `import Mathlib` explicitly for arithmetic and tactic support.
- Use `import PVsNpLib` for the shared `IsPolynomial` definition.
- The witness in the NP statement can be ignored; the verifier only needs the first half of the combined input.
- `verifier_iff` is already proven; focus first on `liftCircuit_eval` and then on the well-formedness bypass.
