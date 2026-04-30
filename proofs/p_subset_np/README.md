# Problem: P ⊆ NP

Formally prove the standard inclusion `P ⊆ NP` in the circuit model already used by the main `p_versus_np` track.
This folder is kept only because solving it materially strengthens the same formal framework needed for the repository's P vs NP work.

| Approach | Priority | Status | Relationships |
|----------|----------|--------|---------------|
| [circuit-lifting](circuit-lifting/) | 60 | ✅ Complete — `p_subset_np` proven; 0 `sorry`s | Supports `p_versus_np/circuit-lower-bounds` by proving the easy inclusion `P ⊆ NP` and verifier lifting once in the shared model; frozen unless the main route needs a specific reusable lemma |

## Project-Leader Notes

- This track is now complete. `p_subset_np` is proven with no `sorry`s via circuit sanitization.
- This folder is **frozen**: do not add new problems or approaches here.
- If the main `p_versus_np/circuit-lower-bounds` route needs a specific reusable lemma (e.g., sanitization utilities), it may import from here or the relevant lemma may be promoted to `lib/`.
- Do not add unrelated follow-on problems under this folder.
