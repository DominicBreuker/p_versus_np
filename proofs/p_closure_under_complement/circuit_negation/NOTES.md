# Progress Notes — P is Closed Under Complement

**Last Updated:** 2026-04-29 (created by Project Leader)

**Status:** New — stub created; no proofs yet

---

## Progress

- [ ] Task 1: Copy circuit definitions (Language, inP, BoolCircuit, etc.)
- [ ] Task 2: Define `complement : Language → Language`
- [ ] Task 3: Define `negateCircuit`
- [ ] Task 4: Prove `negateCircuit_size`
- [ ] Task 5: Prove `negateCircuit_eval`
- [ ] Task 6: Prove `poly_succ`
- [ ] Task 7: Prove `p_closed_under_complement`

## Motivation

This is the most immediately achievable sorry-free theorem in the repository beyond the
already-proven `inDTIME_mono` and `inDTIME_congr` (in the THT track).
The circuit model already has all the components needed:
- `BoolCircuit`, `evalCircuit`, `inP` are defined.
- Adding a NOT gate and showing it flips the output is elementary.
- No open-problem axioms are required.

## Next Steps

1. Copy the self-contained circuit definitions from `proofs/p_subset_np/circuit-lifting/Proof.lean`.
2. Define `complement` and `negateCircuit`.
3. Prove `negateCircuit_eval` using `Array.foldl_push` and `Array.getD_push_eq`.
4. Assemble `p_closed_under_complement`.

## Obstacles / Questions

- Finding the exact Lean4/Mathlib lemma names for `Array.foldl_push` and `Array.getD_push_eq`.
  Search with `lean_loogle` or `lean_leansearch` for `Array.push` lemmas.
- The `Bool.not_eq_true` and `Bool.eq_false_iff_ne_true` simp lemmas may be useful for the
  final iff direction in the correctness proof.
