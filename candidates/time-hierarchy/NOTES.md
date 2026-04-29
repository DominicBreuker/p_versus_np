# Progress Notes — Time Hierarchy Theorem

**Last Updated:** 2026-04-29 (Project Leader review)

**Status:** Active — monotonicity proven; diagonalization stalled

---

## Progress

- [x] Task 1: Define abstract machine model (`Decider`, `decides`, `timeOf`)
- [x] Task 2: Define `inDTIME f`
- [x] Task 3: Prove `inDTIME_mono` (no sorry — clean one-liner proof)
- [x] Task 4: Prove `inDTIME_congr` (no sorry — using `inDTIME_mono` twice)
- [ ] Task 5: Define `encode : Nat → List Bool → List Bool` concretely
- [ ] Task 6: Define `universal : Decider` concretely (axiom is in place)
- [ ] Task 7: Construct diagonalizing language D
- [ ] Task 8: Prove D ∈ DTIME(g)
- [ ] Task 9: Prove D ∉ DTIME(f)
- [ ] Task 10: Complete `time_hierarchy_theorem` proof

## Current Work

Initial stub created 2026-04-28. Two lemmas proven sorry-free:
- `inDTIME_mono`: if `f ≤ g` pointwise, then `inDTIME f L → inDTIME g L`.
- `inDTIME_congr`: if `f = g` pointwise, then `inDTIME f L ↔ inDTIME g L`.

The monotonicity direction of `time_hierarchy_theorem` also compiles (uses `inDTIME_mono`).
The diagonalization direction uses `sorry`.

## Next Steps

1. **Define `encode` concretely** — use `List.replicate i false ++ [true] ++ w` as the pairing
   function. This avoids any sorry for the encoding itself.
2. **Construct the diagonal language** using `universal` and `encode`.
3. **Prove the two membership claims** for the diagonal language.

## Obstacles / Questions

- `timeOf` is noncomputable (uses `sorry`); the `universal_simulation` axiom bridges this gap.
- The universal simulation bound uses quadratic overhead (`f(n) * (f(n) + 1)`), which means
  the THT gap condition is `∀ n, f n * (f n + 1) < g n`. For f = n, this requires g(n) > n²+n,
  so `g = n³` (or any superquadratic polynomial) works for the concrete instantiation.
- Full formalization requires Lean4's `Nat` arithmetic lemmas; avoid `omega` for complex exponential goals.

