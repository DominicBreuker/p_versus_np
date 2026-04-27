# Repository Agent Instructions

- Read `README.md`, `BOOTSTRAP.md`, `candidates/README.md`, and the current idea files before making changes.
- This repository is primarily a Lean4 project. Match the existing Lean style and keep changes small.
- For researcher runs, the intended writable files are the current idea's `NOTES.md` and `Proof.lean`, plus `lib/utils.lean` only when shared code is required.
- Never rewrite `README.md` files during a researcher run.
- Run `lake build` and direct Lean file checks when the toolchain is available.
- Do not commit or push unless the task explicitly requires git operations.
