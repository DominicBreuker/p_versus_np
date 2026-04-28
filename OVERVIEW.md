# Project Overview

**Last Updated:** 2026-04-28 (Project Leader run)

---

## Goal

Formally prove or disprove **P = NP** using Lean4.

## Current Ideas

| Idea | Priority | Status |
|------|----------|--------|
| [circuit-lower-bounds](candidates/circuit-lower-bounds/) | High | Active — stalled at initial stub |
| [time-hierarchy](candidates/time-hierarchy/) | High | Active — new; concrete THT formalization |

## Progress Summary

- **Active Ideas:** 2
- **Stalled Ideas:** 0
- **Dead Ends:** 0
- **Proofs Completed:** 0

## Assessment (2026-04-28)

### circuit-lower-bounds
- Created 2026-04-27. All 6 tasks remain at the stub/pending stage.
- The `Proof.lean` has reasonable data-structure definitions (`Gate`, `BoolCircuit`, `evalNode`)
  but `evalCircuit` still uses `sorry`, and both `inP` and `inNP` have structural issues.
- **Action taken:** README updated with concrete code snippets to fix `evalCircuit`,
  `IsPolynomial`, and `inNP` witness encoding. Researchers should tackle these next.

### time-hierarchy (new, 2026-04-28)
- New idea added to diversify the research portfolio.
- Targets the **Deterministic Time Hierarchy Theorem** (proven result, not an open problem).
- Formalizing it gives a concrete, achievable milestone and a reusable complexity-class framework.
- Initial `Proof.lean` stub provides abstract `Decider`/`DTIME` definitions and a
  provable warm-up lemma (`DTIME_mono`).
- **Recommended first task:** implement `DTIME_mono` and `DTIME_const_subset`.

## Next Steps

- Researchers: advance the circuit-lower-bounds proof (`evalCircuit` fix is the blocker).
- Researchers: run `DTIME_mono` to zero for time-hierarchy as a first clean proof.
- Project Leader (next run, ~8 h): re-assess both ideas; demote circuit-lower-bounds if
  still stalled; promote time-hierarchy if monotonicity lemma is done.

