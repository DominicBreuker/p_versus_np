# Repository Agent Instructions

- Read `README.md`, `BOOTSTRAP.md`, `proofs/README.md`, `references/README.md`, and the current target files before making changes.
- This repository is primarily a Lean4 project. Match the existing Lean style and keep changes small.
- Lean tooling is expected to be available before you start: `lean`, `lake`, Mathlib cache, `rg`, and the `lean-lsp` MCP server.
- Prefer Lean MCP tools over blind guessing when working on `.lean` files:
  - `lean_diagnostic_messages` for fast per-file errors/warnings
  - `lean_goal` / `lean_term_goal` to inspect proof states
  - `lean_local_search`, `lean_leansearch`, `lean_loogle`, and `lean_leanfinder` to find existing lemmas
  - `lean_multi_attempt` to compare tactic candidates
  - `lean_verify` before claiming a proof is complete or sound
- Shared library modules are imported with `import PVsNpLib` or `import PVsNpLib.Utils`; do not try to import raw `lib/...` paths.
- Use `import Mathlib` explicitly in proof files when you need Mathlib lemmas or tactics.
- A good Lean workflow is: inspect diagnostics/goals → search for existing lemmas → try candidate tactics/proof terms → re-check diagnostics and soundness → finish with `lake build`.
- Use `lake build` for whole-project checkpoints, but use Lean MCP diagnostics first for faster iteration.
- For researcher runs, the intended writable files are the current target's `NOTES.md` and `Proof.lean`, plus `lib/utils.lean` only when shared code is required.
- Never rewrite `README.md` files during a researcher run.
- Run `lake build` and direct Lean file checks when the toolchain is available.
- Do not commit or push unless the task explicitly requires git operations.
