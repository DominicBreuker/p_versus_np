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
- [x] Task 7: State Cook–Levin theorem (axiomatized)
- [ ] Task 8: Prove superpolynomial lower bound
- [ ] Task 9: Complete connection between lower bounds and P ≠ NP

## Current Work

- `evalCircuit`, `inP`, and `inNP` are implemented as per README guidance.
- Added eight sanity lemmas for `evalCircuit`:
  - `evalCircuit_const_true`: single Const true node → true
  - `evalCircuit_const_false`: single Const false node → false  
  - `evalCircuit_var_zero`: single Var 0 node → input bit 0 (requires n > 0)
  - `evalCircuit_not`: NOT gate negates its child
  - `evalCircuit_and_true_true`: AND with two true children → true
  - `evalCircuit_and_true_false`: AND with true and false → false
  - `evalCircuit_or_false_false`: OR with two false children → false
  - `evalCircuit_or_true_false`: OR with true and false → true
- `IsPolynomial` moved to `lib/utils.lean` under `PVsNpLib` namespace
- Cook–Levin theorem axiomatized as `sat_is_np_complete`
- Added `sat_superpolynomial_implies_p_neq_np` lemma connecting circuit lower bounds to P ≠ NP

The main theorem `p_neq_np` remains as `sorry`.

## Next Steps

1. Complete the proof of `sat_superpolynomial_implies_p_neq_np`
2. Work on Shannon counting argument for lower bounds
3. Formalize the superpolynomial lower bound for SAT

## Obstacles / Questions

- Need to verify the circuit evaluation lemmas compile correctly
- The Var node indexing needs careful handling for edge cases (n = 0)
- The `sat_superpolynomial_implies_p_neq_np` lemma needs completion
