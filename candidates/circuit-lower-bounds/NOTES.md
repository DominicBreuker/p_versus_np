# Progress Notes

**Last Updated:** 2026-04-28

**Status:** Active

---

## Progress

- [x] Task 1: Formalize Boolean circuit definitions (BoolCircuit, Gate, CircuitNode)
- [x] Task 2: Fix evalCircuit — implemented using foldl over node array
- [x] Task 3: Define IsPolynomial predicate and update inP
- [x] Task 4: Fix inNP witness encoding using omega tactic
- [x] Task 5: Add sanity lemmas for evalCircuit (const_true, const_false, var_zero)
- [x] Task 6: Move IsPolynomial to lib/utils.lean for reuse
- [ ] Task 7: State Cook–Levin theorem
- [ ] Task 8: Prove superpolynomial lower bound
- [ ] Task 9: Connect lower bound to P ≠ NP

## Current Work

- `evalCircuit`, `inP`, and `inNP` are implemented as per README guidance.
- Added three sanity lemmas for `evalCircuit`:
  - `evalCircuit_const_true`: single Const true node → true
  - `evalCircuit_const_false`: single Const false node → false  
  - `evalCircuit_var_zero`: single Var 0 node → input bit 0 (requires n > 0)
- `IsPolynomial` moved to `lib/utils.lean` under `PVsNpLib` namespace

The main theorem `p_neq_np` remains as `sorry`.

## Next Steps

1. Add more circuit lemmas (AND, OR, NOT gates composition)
2. State Cook–Levin theorem (axiomatize if needed)
3. Work on Shannon counting argument for lower bounds

## Obstacles / Questions

- Need to verify the circuit evaluation lemmas compile correctly
- The Var node indexing needs careful handling for edge cases (n = 0)
