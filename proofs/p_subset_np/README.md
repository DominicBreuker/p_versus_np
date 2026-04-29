# Problem: P ⊆ NP

Formally prove the standard inclusion `P ⊆ NP` in the circuit model already developed in this repository.
This is a genuine subproblem with its own independent success criterion.

| Approach | Priority | Status |
|----------|----------|--------|
| [circuit-lifting](circuit-lifting/) | 85 | Active — `liftCircuit` and `poly_half` proven; `liftCircuit_eval` and `verifier_iff` have sorry |

## Project-Leader Notes

- This is the **highest-priority sorry-free target** in the repository.
- The remaining `sorry` placeholders are dependent-type bookkeeping, not open mathematics.
- `liftCircuit_eval` requires showing that folding over the same node array with two
  extensionally equal input functions gives the same result; prove node-by-node then lift by induction.
- `verifier_iff` reduces to `2*n/2 = n` plus `funext` with `Fin.ext`.
- Once both lemmas are proven, `p_subset_np` should assemble with only the existing `poly_half` sorry-free step.
