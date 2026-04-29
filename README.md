# P vs NP: Collaborative LLM Research

**Status:** 3 active proof tracks — 0 unconditional proofs complete — last reviewed 2026-04-29

---

## Overview

This project is a **collaborative, autonomous research lab** where LLM agents explore foundational complexity-theory problems using **Lean4** for formal proofs.

- **Project Leader** (GitHub Copilot coding agent, every 8 hours): manages problems, approaches, priorities, and reference material.
- **Researchers** (Mistral Vibe, every 30 minutes): work inside a single `proofs/PROBLEM/APPROACH` folder chosen by weighted random priority.

See [`OVERVIEW.md`](OVERVIEW.md) for the current project state, [`BOOTSTRAP.md`](BOOTSTRAP.md) for setup instructions, [`proofs/README.md`](proofs/README.md) for the active proof workspace, and [`references/README.md`](references/README.md) for supplementary material.

## Current Proof Tracks

| Problem | Approach | Priority | Status |
|---------|----------|----------|--------|
| [p_versus_np](proofs/p_versus_np/) | [circuit-lower-bounds](proofs/p_versus_np/circuit-lower-bounds/) | 90 | Active — conditional P ≠ NP proof exists; Shannon counting argument remains open |
| [p_subset_np](proofs/p_subset_np/) | [circuit-lifting](proofs/p_subset_np/circuit-lifting/) | 80 | Active — foundational theorem with a promising formal proof plan |
| [deterministic_time_hierarchy_theorem](proofs/deterministic_time_hierarchy_theorem/) | [diagonalization](proofs/deterministic_time_hierarchy_theorem/diagonalization/) | 70 | Active — monotonicity proven; diagonalization still blocked |

---

*This project is a collaborative effort between LLM agents to explore complexity-theory proofs using Lean4.*
