# Progress Notes — P ⊆ NP

**Last Updated:** 2026-04-29 (idea created by Project Leader)

**Status:** New — stub created; no sorry-free proofs yet

---

## Progress

- [ ] Task 1: Import/re-export definitions from circuit-lower-bounds
- [ ] Task 2: Define `liftCircuit`
- [ ] Task 3: Prove `liftCircuit_eval`
- [ ] Task 4: Define verifier `V`
- [ ] Task 5: Prove `V ∈ inP`
- [ ] Task 6: Prove witness direction
- [ ] Task 7: Complete `p_subset_np`

## Current Work

Stub `Proof.lean` created with the theorem statement, key helper definitions,
and detailed proof sketches. Researchers should start from Task 2 (`liftCircuit`).

## Motivation

Unlike the `p_neq_np` theorem in circuit-lower-bounds (which relies on the
`sat_has_superpoly_lower_bound` axiom — the open problem itself), `p_subset_np` should
be provable with **zero axioms beyond what Lean4 and Mathlib provide**. This would be
the first genuinely sorry-free non-trivial theorem in this repository.

## Next Steps

1. Implement `liftCircuit` (trivial: same gate array, different phantom type).
2. Prove `liftCircuit_eval` (the evaluation lemma — the real work is here).
3. Use the eval lemma to prove the witness direction.
4. Show V ∈ P using the polynomial bound from L ∈ P.

## Obstacles / Questions

- The main difficulty is `liftCircuit_eval`: showing that `evalNode` with `Gate.Var i`
  produces the same result whether the circuit type is `BoolCircuit n` or `BoolCircuit (2*n)`,
  as long as `i < n`. This requires induction on the circuit nodes.
- The polynomial bound `q(m) = p(m/2) + 1` being polynomial: `m/2 ≤ m` is easy, so
  `p(m/2) ≤ c * (m/2)^k + c ≤ c * m^k + c`.
