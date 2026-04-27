# P vs NP Collaborative LLM Research — Bootstrap Guide

This file documents how the repository was bootstrapped and how to set up a fresh instance.

---

## Overview

This repository is a **self-sustaining, autonomous research lab** where LLM agents explore
the **P vs NP problem** using **Lean4** for formal proofs.

| Agent | Runs | Model | API Key Secret |
|---|---|---|---|
| Project Leader | Every 8 hours | GPT-4o (configurable) | `OPENAI_API_KEY` |
| Researcher | Every 30 minutes | Mistral Large (configurable) | `MISTRAL_VIBE_KEY` |

---

## Repository Structure

```
.
├── .github/
│   ├── scripts/
│   │   ├── project_leader.py   # Project Leader LLM agent
│   │   └── researcher.py       # Researcher LLM agent
│   └── workflows/
│       ├── project_leader.yml  # Runs project_leader.py every 8 h
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
| `OPENAI_API_KEY` | Your OpenAI API key |

### 3. (Optional) Add Repository Variables

Go to **Settings → Secrets and variables → Actions → Variables** and optionally add:

| Variable name | Default | Description |
|---|---|---|
| `OPENAI_MODEL` | `gpt-4o` | OpenAI model for Project Leader |
| `MISTRAL_MODEL` | `mistral-large-latest` | Mistral model for Researcher |

### 4. Enable GitHub Actions

Go to **Settings → Actions → General** and ensure Actions are enabled.

### 5. Trigger the first run

- Go to **Actions → Project Leader → Run workflow** to generate the first ideas.
- After that, the scheduled workflows will run automatically.

---

## How the System Works

### Communication via files

All agent communication happens through committed files — no direct API calls between agents.

| File | Written by | Read by |
|---|---|---|
| `candidates/README.md` | Project Leader | Researchers |
| `candidates/<idea>/README.md` | Project Leader | Researchers |
| `candidates/<idea>/NOTES.md` | Researchers | Project Leader, Researchers |
| `candidates/<idea>/Proof.lean` | Researchers | Project Leader (review) |
| `lib/utils.lean` | Researchers (on instruction) | Researchers |
| `OVERVIEW.md`, `README.md` | Project Leader | Humans |

### Idea lifecycle

1. **Generation** — Project Leader creates `candidates/<idea-name>/` with boilerplate.
2. **Research** — Researcher picks the highest-priority active idea and advances the proof.
3. **Review** — Project Leader reviews progress, updates priorities and hints.
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

# Download prebuilt Mathlib cache (much faster than building from source)
lake exe cache get

# Build the project
lake build
```

---

## Agent Prompts

### Project Leader system prompt

> You are the project leader for the "P vs NP" research project. You are a senior mathematics
> researcher with deep expertise in theoretical computer science and formal proof systems (Lean4).
> Your role is to generate ideas, manage priorities, review progress, and update documentation.

Full prompt: [`.github/scripts/project_leader.py`](.github/scripts/project_leader.py)

### Researcher system prompt

> You are a researcher working on the "P vs NP" problem. You are an expert in Lean4 and formal
> theorem proving. Your role is to extend Lean4 proofs and track progress in NOTES.md.

Full prompt: [`.github/scripts/researcher.py`](.github/scripts/researcher.py)
