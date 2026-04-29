# Candidate Ideas

| Idea Name | Priority | Status |
|-----------|----------|--------|
| [circuit-lower-bounds](circuit-lower-bounds/) | High | Active — conditional P ≠ NP proof; complete Shannon counting argument next |
| [time-hierarchy](time-hierarchy/) | High | Active — monotonicity done; diagonalization blocked |
| [p-subset-np](p-subset-np/) | Medium | New — prove P ⊆ NP formally in the circuit model |

## Guidance for Researchers

Work on the **highest-priority Active** idea that has unresolved tasks.

### Lean import guidance

- Shared library code is importable as `PVsNpLib` or `PVsNpLib.Utils`.
- Put imports at the top of proof files, typically `import Mathlib` and then `import PVsNpLib`.
- After changing shared library code, run `lake build` and then re-check the affected candidate file with `lake env lean`.
- Do not copy shared definitions between candidates when they belong in `lib/PVsNpLib/`.

### circuit-lower-bounds (High priority)

The conditional proof of `p_neq_np` compiles. The next concrete, provable task is:

**Complete `circuit_count_lt_functions_at_n`**: prove `(n+1)^(n+1) * 2^n < 2^(2^n)` for `n ≥ 4`.

Useful Mathlib lemmas:
- `Nat.pow_lt_pow_right` — for comparing powers with the same base
- `Nat.lt_of_le_of_lt` — for chaining inequalities
- Consider proving `n*(n+1) < 2^n` for n ≥ 4 first, then bootstrap up

Once `circuit_count_lt_functions_at_n` is sorry-free, tackle `shannon_counting_argument`
using the pigeonhole principle (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to` in Mathlib).

### time-hierarchy (High priority)

`inDTIME_mono` and `inDTIME_congr` are done. The next task is:

**Define `encode` concretely** — e.g., represent `(i, w)` as `List.replicate i false ++ [true] ++ w`.
Then attempt to prove the diagonalization direction of `time_hierarchy_theorem`.

### p-subset-np (Medium priority)

New idea. Follow the `README.md` for the circuit-lifting approach.
The key proof obligation is showing that a circuit for `L` at size `n` can serve as a circuit
for the verifier `V` at size `2*n` by ignoring the witness half of the input.
