# P vs NP Collaborative LLM Research — Bootstrap Guide

This file documents how the repository was bootstrapped and how to set up a fresh instance.

---

## Overview

This repository is a **self-sustaining, autonomous research lab** where LLM agents explore
the **P vs NP problem** using **Lean4** for formal proofs.

| Agent | Runs | Model | Auth / Secret |
|---|---|---|---|
| Project Leader | Every 8 hours | GitHub Copilot coding agent (request strongest reasoning/math model in issue prompt) | `GH_PAT` |
| Researcher | Every 30 minutes | Mistral Vibe (configurable model) | `MISTRAL_VIBE_KEY` |

---

## Repository Structure

```
.
├── .github/
│   ├── prompts/
│   │   └── project_leader_issue.md  # Issue prompt for Copilot Project Leader
│   ├── scripts/
│   │   ├── create_copilot_issue.py  # Creates & assigns Copilot issues
│   │   └── researcher.py            # Researcher LLM agent
│   └── workflows/
│       ├── copilot-setup-steps.yml # Prepares Copilot cloud agent environment
│       ├── project_leader.yml  # Creates and assigns a Copilot issue every 8 h
│       ├── researcher.yml      # Runs researcher.py every 30 min
│       └── lean_check.yml      # Verifies Lean4 proofs on every push
├── candidates/
│   ├── README.md               # Priority table (managed by Project Leader)
│   └── <idea-name>/
│       ├── README.md           # Problem statement & hints (Project Leader)
│       ├── NOTES.md            # Progress log (Researcher)
│       └── Proof.lean          # Lean4 proof (Researcher)
├── lib/
│   ├── __init__.lean           # Library entry point
│   └── utils.lean              # Reusable Lean4 definitions
├── lean-toolchain              # Lean4 toolchain version
├── lakefile.lean               # Lake build configuration
├── README.md                   # Project status (auto-updated)
├── OVERVIEW.md                 # Detailed project state (auto-updated)
└── BOOTSTRAP.md                # This file
```

---

## Setup Instructions

### 1. Fork / create the repository

Start with an empty GitHub repository (or fork this one).

### 2. Add GitHub Secrets

Go to **Settings → Secrets and variables → Actions → Secrets** and add:

| Secret name | Value |
|---|---|
| `MISTRAL_VIBE_KEY` | Your Mistral API key |
| `GH_PAT` | GitHub token/PAT with permission to create issues and assign Copilot |

### 3. (Optional) Add Repository Variables

Go to **Settings → Secrets and variables → Actions → Variables** and optionally add:

| Variable name | Default | Description |
|---|---|---|
| `MISTRAL_MODEL` | *(Vibe default)* | Optional Mistral Vibe model override for Researcher |

### 4. Enable GitHub Actions

Go to **Settings → Actions → General** and ensure Actions are enabled.

### 5. Copilot cloud agent bootstrap

The repository includes `.github/workflows/copilot-setup-steps.yml`, which preinstalls:

- Lean / Lake plus cached `.lake` artifacts via `leanprover/lean-action`
- `rg` for local theorem/source search
- the `lean-lsp-mcp` server used by the Project Leader

For reproducibility, the repository also commits `lake-manifest.json` and pins
`lean-toolchain` to the exact Lean release required by Mathlib.

This workflow must exist on the default branch before Copilot cloud-agent sessions can benefit from it.

### 6. Trigger the first run

- Go to **Actions → Project Leader → Run workflow** to create and assign the first Copilot Project Leader issue.
- After that, the scheduled workflows will run automatically.

---

## How the System Works

### Communication via files

All agent communication happens through committed files and GitHub issues — no direct inter-agent API calls.

| File | Written by | Read by |
|---|---|---|
| `candidates/README.md` | Project Leader | Researchers |
| `candidates/<idea>/README.md` | Project Leader | Researchers |
| `candidates/<idea>/NOTES.md` | Researchers | Project Leader, Researchers |
| `candidates/<idea>/Proof.lean` | Researchers | Project Leader (review) |
| `lib/utils.lean` | Researchers (on instruction) | Researchers |
| `OVERVIEW.md`, `README.md` | Project Leader | Humans |
| Project Leader issue | Workflow | GitHub Copilot coding agent |

### Idea lifecycle

1. **Kickoff** — The Project Leader workflow creates a GitHub issue and assigns the GitHub Copilot coding agent to it.
2. **Generation / Review** — The Project Leader reviews progress, updates priorities and hints, and creates new ideas when needed.
3. **Research** — Researcher picks the highest-priority active idea and advances the proof.
4. **Success / Dead End** — Project Leader declares success (no `sorry`) or archives the idea.
5. **Pivot** — If all ideas are dead ends, Project Leader generates new ones.

---

## Lean4 Proof Verification

The `lean_check.yml` workflow runs `lake build` on every push that touches `.lean` files.
Only proofs that compile without `sorry` are considered complete.

To check locally:
```bash
# Install elan (Lean toolchain manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Sync the committed dependency manifest
lake update

# Download prebuilt Mathlib cache (much faster than building from source)
lake exe cache get

# Build the project
lake build
```

---

## Agent Prompts

### Project Leader issue prompt

> Use the utmost capable logic, mathematics, and reasoning model available to the GitHub Copilot
> coding agent for this issue. This task is primarily about deep mathematical reasoning, formal
> proof strategy, repository-wide planning, and careful document curation.

Full prompt: [`.github/prompts/project_leader_issue.md`](.github/prompts/project_leader_issue.md)

### Researcher system prompt

> You are a researcher working on the "P vs NP" problem. You are an expert in Lean4 and formal
> theorem proving. Your role is to extend Lean4 proofs and track progress in NOTES.md.

Prompt template: [`.github/prompts/researcher_vibe.md`](.github/prompts/researcher_vibe.md)

---

## Lean MCP support

Both agent environments are configured to have access to the [`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp) server.

- **Project Leader / Copilot cloud agent** uses the repository-scoped `.mcp.json` definition together with `copilot-setup-steps.yml`.
- **Researcher / Mistral Vibe** writes a `~/.vibe/config.toml` entry during the workflow before invoking `vibe`.

Use the Lean MCP tools for fast diagnostics (`lean_diagnostic_messages`), goal inspection (`lean_goal`), theorem search (`lean_local_search`, `lean_leansearch`, `lean_loogle`, `lean_leanfinder`), tactic comparison (`lean_multi_attempt`), and proof soundness checks (`lean_verify`) before relying on full `lake build` runs.

The researcher workflow installs Mistral Vibe with Python 3.12 and validates the
checked-in Lake manifest before launching the agent so that both agent environments
start from the same Lean and dependency state.
