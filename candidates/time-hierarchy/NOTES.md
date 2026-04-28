# Progress Notes — Time Hierarchy Theorem

**Last Updated:** 2026-04-28 (initial)

**Status:** Active — new idea

---

## Progress

- [ ] Task 1: Define abstract machine model (`Decider`, `decides`, `timeOf`)
- [ ] Task 2: Define `DTIME f`
- [ ] Task 3: Define `IsTimeConstructible` and little-o relation
- [ ] Task 4: State universal simulation axiom
- [ ] Task 5: Construct diagonalizing language D
- [ ] Task 6: Prove D ∈ DTIME(g)
- [ ] Task 7: Prove D ∉ DTIME(f)
- [ ] Task 8: Conclude DTIME(f) ⊊ DTIME(g)
- [ ] Task 9 (bonus): Instantiate for f = n, g = n²

## Current Work

Initial stub created with abstract definitions and monotonicity lemma skeleton.

## Next Steps

1. Flesh out `Decider` definitions and `DTIME` in `Proof.lean`.
2. Prove `DTIME_mono` (monotonicity) as a warm-up.
3. Axiomatize `timeOf` and the universal simulation bound.
4. Sketch the diagonal language D and its properties.

## Obstacles / Questions

- Full Turing machine formalization is heavyweight; using an abstract `Decider` type avoids this.
- The universal simulation axiom is the key assumption; it is classically provable but may be
  deferred as `axiom` in Lean4 to keep progress moving.
- Encoding of `(i, w)` pairs as `List Bool` needs a concrete pairing function.
