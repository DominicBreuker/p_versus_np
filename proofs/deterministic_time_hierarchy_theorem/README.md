# Problem: Deterministic Time Hierarchy Theorem

Formally prove the deterministic time hierarchy theorem in Lean4.
This is a separate theorem, not a direct proof of `P versus NP`, but it is a valuable benchmark problem for the repository.

| Approach | Priority | Status |
|----------|----------|--------|
| [diagonalization](diagonalization/) | 70 | Active — monotonicity proven (sorry-free); encoding defined; diagonalization construction pending |

## Project-Leader Notes

- Tasks 1–6 are complete and sorry-free (`inDTIME_mono`, `inDTIME_congr`, `encode_length`).
- The blocking step is the construction of the diagonal language and the two membership proofs.
- The `universal` decider is backed by `universal_simulation` axiom — do not try to implement it concretely.
- Focus on Tasks 7–9 in `diagonalization/README.md`; completing these would give the first proved theorem in this track.
