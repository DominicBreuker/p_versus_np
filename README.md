# P vs NP: Collaborative Lean4 Research

**Status:** 2 proof tracks — 1 direct `P ≠ NP` route (active) — 1 supporting track (complete) — last reviewed 2026-04-30

---

## Overview

This repository exists for one purpose only: **solve the P vs NP problem in Lean4**.

Everything in the repository must serve that goal.

- **Project Leader** (GitHub Copilot coding agent, every 8 hours): curates proof directions for settling `P = NP` or `P ≠ NP`, maintains priorities, and keeps the workspace tightly scoped to material steps toward that goal.
- **Researchers** (Mistral Vibe, every 30 minutes): work inside one approved proof target under `proofs/` and make the smallest useful step toward that target.

The Project Leader must not introduce random complexity-theory problems. A non-`p_versus_np` problem may exist under `proofs/` only when solving it would be a **material step forward** for an already-documented P vs NP proof approach, and that relationship must be recorded explicitly in the proof tables.

See [`OVERVIEW.md`](OVERVIEW.md) for the current project state, [`BOOTSTRAP.md`](BOOTSTRAP.md) for setup instructions, [`proofs/README.md`](proofs/README.md) for the active proof workspace, and [`references/README.md`](references/README.md) for supplementary material.

## Current Proof Tracks

| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — Task 6 complete; Task 7 in progress; **3 `sorry`s remain** (`evalCircuit_normalizeCircuit`; `poly_quadratic_bound_k_ge_1`; pigeonhole step in `shannon_counting_argument`); `evalNode_normalizeNodeCode` closed 2026-04-30; `p_neq_np` compiles conditionally on two axioms | Direct attack on `P ≠ NP`; the support track exists only to finish shared circuit-model infrastructure this route reuses |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 0 | ✅ Complete — `p_subset_np` proven; 0 `sorry`s; track frozen | Supplies the easy inclusion `P ⊆ NP` in the shared circuit model; complete and no further work planned unless main route needs a specific reusable lemma |

---

*This repository is a focused Lean4 research workspace for settling P vs NP, not a general complexity-theory playground.*
