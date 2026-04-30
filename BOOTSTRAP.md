# P vs NP Collaborative Lean4 Research — Bootstrap Guide

This file documents how the repository was bootstrapped and how to set up a fresh instance.

---

## Overview

This repository is a **self-sustaining Lean4 research workspace whose single purpose is to solve the P vs NP problem**.

Every workflow, prompt, proof target, and reference file should be evaluated against that objective.

| Agent | Runs | Model | Auth / Secret |
|---|---|---|---|
| Project Leader | Every 8 hours | GitHub Copilot coding agent (request strongest reasoning/math model in issue prompt) | `GH_PAT` |
| Researcher | Every 30 minutes | Mistral Vibe (configurable model) | `MISTRAL_VIBE_KEY` / `MISTRAL_LABS_KEY` |

---

## Repository Structure

```
.
├── .github/
│   ├── prompts/
│   │   └── project_leader_issue.md  # Project Leader prompt focused on P vs NP
│   ├── scripts/
│   │   ├── create_copilot_issue.py  # Creates & assigns Copilot issues
│   │   └── researcher.py            # Researcher LLM agent
│   └── workflows/
│       ├── copilot-setup-steps.yml  # Prepares Copilot cloud agent environment
│       ├── project_leader.yml       # Creates and assigns a Copilot issue
│       ├── researcher.yml           # Runs researcher.py
│       └── lean_check.yml           # Verifies Lean4 proofs
├── proofs/
│   ├── README.md                    # Global priority table with relationships (managed by Project Leader)
│   └── <problem>/
│       ├── README.md                # Problem overview and relationship to P vs NP
│       └── <approach>/
│           ├── README.md            # Approach statement & hints (Project Leader)
│           ├── NOTES.md             # Progress log (Researcher)
│           └── Proof.lean           # Lean4 proof (Researcher)
├── references/
│   ├── README.md                    # Index of supplementary reference documents
│   └── ...                          # Human-provided notes, papers, reviews, etc.
├── lib/
│   ├── PVsNpLib.lean
│   ├── PVsNpLib/
│   │   └── Utils.lean
│   ├── __init__.lean
│   └── utils.lean
├── lean-toolchain
├── lakefile.lean
├── README.md
├── OVERVIEW.md
└── BOOTSTRAP.md
```

---

## Setup Instructions

### 1. Fork / create the repository

Start with an empty GitHub repository (or fork this one).

### 2. Add GitHub Secrets

Go to **Settings → Secrets and variables → Actions → Secrets** and add:

| Secret name | Value |
|---|---|
| `MISTRAL_VIBE_KEY` | Mistral API key for the Devstral/auto-approve researcher run |
| `MISTRAL_LABS_KEY` | Mistral API key for the Lean researcher run |
| `GH_PAT` | GitHub token/PAT with permission to create issues and assign Copilot |

### 3. (Optional) Add Repository Variables

Go to **Settings → Secrets and variables → Actions → Variables** and optionally add:

| Variable name | Default | Description |
|---|---|---|
| `MISTRAL_MODEL` | *(Vibe default)* | Optional Mistral Vibe model override for Researcher |
| `RESEARCHER_RUN_COUNT` | `2` | Optional default number of Vibe passes per researcher invocation |
| `RESEARCHER_OVERALL_TIMEOUT_MINUTES` | `0` | Optional default cumulative Vibe runtime limit in minutes before later passes are skipped (`0` disables the limit) |

### 4. Enable GitHub Actions

Go to **Settings → Actions → General** and ensure Actions are enabled.

### 5. Copilot cloud agent bootstrap

The repository includes `.github/workflows/copilot-setup-steps.yml`, which preinstalls:

- Lean / Lake plus cached `.lake` artifacts via `leanprover/lean-action`
- `rg` for local theorem/source search
- the `lean-lsp-mcp` server used by the agents

### 6. Trigger the first run

- Go to **Actions → Project Leader → Run workflow** to create and assign the first Copilot Project Leader issue.
- Go to **Actions → Researcher → Run workflow** to override the per-run Vibe pass count or cumulative runtime limit for a manual researcher run.
- After that, the scheduled workflows will run automatically.

---

## How the System Works

### Communication via files

All agent communication happens through committed files and GitHub issues — no direct inter-agent API calls.

| File | Written by | Read by |
|---|---|---|
| `proofs/README.md` | Project Leader | Researchers |
| `proofs/<problem>/README.md` | Project Leader | Project Leader, Researchers |
| `proofs/<problem>/<approach>/README.md` | Project Leader | Researchers |
| `proofs/<problem>/<approach>/NOTES.md` | Researchers | Project Leader, Researchers |
| `proofs/<problem>/<approach>/Proof.lean` | Researchers | Project Leader |
| `references/README.md` | Project Leader | Project Leader, Humans |
| `references/*` | Humans, Project Leader | Project Leader |
| `OVERVIEW.md`, `README.md` | Project Leader | Humans |
| Project Leader issue | Workflow | GitHub Copilot coding agent |

### Work lifecycle

1. **Kickoff** — The Project Leader workflow creates a GitHub issue and assigns the GitHub Copilot coding agent to it.
2. **Project leadership** — The Project Leader reviews the active proof tracks, references, and relationships to the main goal.
3. **Research** — The Researcher picks one approved proof target randomly with probability proportional to the numeric priority.
4. **Success / Dead End** — The Project Leader records success, stalls, or retirement conservatively.
5. **Expansion** — The Project Leader may create a new `proofs/<problem>/...` entry only when the new problem is a material subproblem of an already-existing P vs NP proof route and the relationship is documented in the tables.

---

## Lean4 Proof Verification

The `lean_check.yml` workflow is manually triggered with **Run workflow** and checks every
`proofs/*/*/Proof.lean` file with `lake env lean`.
It is meant to verify that proof files are executable Lean files; `sorry` warnings are acceptable.

To check locally:
```bash
lake exe cache get
lake build
```

Shared library code is imported from proof files with:

```lean
import Mathlib
import PVsNpLib
```

or, for a narrower import:

```lean
import PVsNpLib.Utils
```

Do not try to import raw file paths under `lib/`; Lake only resolves module names.

---

## Agent Prompts

- Project Leader prompt: `.github/prompts/project_leader_issue.md`
- Researcher prompt: `.github/prompts/researcher_vibe.md`

---

## Lean MCP support

Both agent environments are configured to have access to the `lean-lsp-mcp` server.
Use Lean MCP tooling for fast diagnostics before relying on full `lake build` runs.
