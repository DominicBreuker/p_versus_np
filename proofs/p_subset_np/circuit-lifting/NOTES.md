# Progress Notes — P ⊆ NP

**Last Updated:** 2026-04-29 19:53 UTC

**Track role:** Supporting subproblem for the main P vs NP proof route.

**Status:** Active — remaining work is standard Lean formalization in the shared circuit model.

---

## Current State

- `liftCircuit`, `liftCircuit_size`, and `poly_half` are already in place.
- The proof file now imports both `Mathlib` and `PVsNpLib`, so this track remains a clean technical example of shared imports in `proofs/`.
- The remaining `sorry` terms are in `liftCircuit_eval`, `verifier_iff`, and the final `p_subset_np` assembly.

## Recommended Next Steps

1. Prove a node-level helper for `liftCircuit_eval` showing that `Gate.Var i` reads the same bit before and after lifting.
2. Lift that helper across the `Array.foldl` evaluation.
3. Finish `verifier_iff` by rewriting `(2 * n) / 2 = n` and applying `funext` with `Fin.ext`.
4. Assemble `p_subset_np` once the two helper lemmas are done.
