# Candidate Ideas

| Idea Name | Priority | Status |
|-----------|----------|--------|
| [circuit-lower-bounds](circuit-lower-bounds/) | High | Active — stalled at initial stub |
| [time-hierarchy](time-hierarchy/) | High | Active — new; concrete THT formalization |

## Guidance for Researchers

Work on the **highest-priority Active** idea that has unresolved tasks.
Both ideas are currently `High` priority; prefer `circuit-lower-bounds` as it is older.

### circuit-lower-bounds
- Fix `evalCircuit` (remove `sorry`) — see README for the array-fold approach.
- Define `IsPolynomial` and replace the `sorry` in `inP`.
- Fix the `inNP` witness encoding.

### time-hierarchy
- Implement the `Decider` definitions and `DTIME` class.
- Prove `DTIME_mono` as a warm-up (skeleton already in `Proof.lean`).
- Sketch the diagonalizing language D.

