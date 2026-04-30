# Problem: P ⊆ NP

Formally prove the standard inclusion `P ⊆ NP` in the circuit model already used by the main `p_versus_np` track.
This folder is kept only because solving it materially strengthens the same formal framework needed for the repository's P vs NP work.

| Approach | Priority | Status | Relationships |
|----------|----------|--------|---------------|
| [circuit-lifting](circuit-lifting/) | 60 | Active — necessary support track; three `sorry`s remain (`liftCircuit_eval`, well-formedness, eval equivalences) | Supports `p_versus_np/circuit-lower-bounds` by proving the easy inclusion `P ⊆ NP` and verifier lifting once in the shared model |

## Project-Leader Notes

- This is a supporting subproblem, not a second repository goal.
- Keep it only as long as it clearly improves the circuit-model foundation used by the main `p_versus_np` route.
- Do not add unrelated follow-on problems under this folder.
- After `p_subset_np` compiles, prefer freezing this folder unless the main route needs a specific reusable lemma from it.
