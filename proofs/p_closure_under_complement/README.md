# Problem: P is Closed Under Complement

Formally prove that the complexity class P is closed under complement in the circuit model:
if L ∈ P then the complement of L is also in P.

| Approach | Priority | Status |
|----------|----------|--------|
| [circuit_negation](circuit_negation/) | 50 | New — stub created; proof should be sorry-free |

## Project-Leader Notes

- This is a well-known, unconditionally provable result.
- It is directly achievable in the current circuit model: complement = add a NOT gate at the circuit output.
- Completing this would give the repository a second sorry-free theorem (alongside `inDTIME_mono`).
- The approach is entirely self-contained within the definitions from `circuit-lower-bounds`.
