# Progress Notes

**Last Updated:** 2026-04-27 (initial)

**Status:** Active

---

## Progress

- [ ] Task 1: Formalize Boolean circuit definitions
- [ ] Task 2: Define polynomial-size circuit families
- [ ] Task 3: Define NP via witnesses
- [ ] Task 4: State Cook–Levin theorem
- [ ] Task 5: Prove superpolynomial lower bound
- [ ] Task 6: Connect lower bound to P ≠ NP

## Current Work

Initial stub created. All tasks pending.

## Next Steps

1. Define `BoolCircuit` as an inductive type in `Proof.lean`.
2. Define `circuitSize` as the number of gates.
3. Prove a basic lemma: every constant function has circuit size 0 or 1.
4. Add any reusable definitions to `lib/utils.lean`.

## Obstacles / Questions

- How to best model circuit depth vs. size in Lean4?
- Should we use `Fin n → Bool` for Boolean functions on n inputs?
