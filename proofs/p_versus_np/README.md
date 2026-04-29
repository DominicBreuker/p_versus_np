# Problem: P versus NP

Formally separate or collapse the relationship between `P` and `NP` in Lean4.
This folder groups approaches whose primary goal is the main repository problem.

| Approach | Priority | Status |
|----------|----------|--------|
| [circuit-lower-bounds](circuit-lower-bounds/) | 90 | Active — conditional P ≠ NP proof compiled; two sorry remain in Shannon counting argument |

## Project-Leader Notes

- The conditional `p_neq_np` proof compiles and is clean: it reduces P ≠ NP to the
  `sat_has_superpoly_lower_bound` axiom (which is the open problem itself) and the
  `sat_is_np_complete` axiom (Cook–Levin, classically provable but laborious).
- The key near-term target is **Task 9**: prove `circuit_count_lt_functions_at_n` for n ≥ 9.
  The n = 4..8 cases already use `decide`. See `circuit-lower-bounds/README.md` for the
  three-step auxiliary-lemma strategy.
- Promote new subproblems to their own `proofs/<problem>/...` folder when they become substantial research targets.
- Keep this README focused on the state of the problem and the available approaches.
