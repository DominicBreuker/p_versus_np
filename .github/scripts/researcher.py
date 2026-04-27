#!/usr/bin/env python3
"""
Researcher Agent for the P vs NP Research Project.

Picks the highest-priority active idea from candidates/README.md,
reads the idea's current state, calls the Mistral API to advance
the proof, and writes the updated files back to the repository.

Required environment variable:
    MISTRAL_VIBE_KEY  — Mistral API key (stored in GitHub secret)

Optional environment variable:
    MISTRAL_MODEL     — Mistral model name (default: mistral-large-latest)
"""

import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

import requests

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

MISTRAL_API_KEY: str = os.environ.get("MISTRAL_VIBE_KEY", "")
MISTRAL_MODEL: str = os.environ.get("MISTRAL_MODEL", "mistral-large-latest")
MISTRAL_API_URL: str = "https://api.mistral.ai/v1/chat/completions"

REPO_ROOT: Path = Path(__file__).resolve().parent.parent.parent

SYSTEM_PROMPT: str = """You are a researcher working on the "P vs NP" problem. \
You are an expert in Lean4 and formal theorem proving. Your role is to:

1. **Task Selection:**
   - You will be given the highest-priority idea to work on.
   - Read the idea's README.md and NOTES.md to understand the current state.

2. **Proof Development:**
   - Extend or write Lean4 code in the idea's Proof.lean.
   - Use the lib/ folder for reusable code if recommended.
   - Follow the hints and problem statement in the idea's README.md.

3. **Progress Tracking:**
   - Update the idea's NOTES.md with:
     - Your progress (e.g., "Proved Lemma X", "Stuck at Step Y").
     - Next steps for the next researcher.
     - Any obstacles or questions.

4. **Library Code:**
   - If instructed in the idea's README.md, factor out reusable code into \
lib/utils.lean.

**Rules:**
- NEVER modify README.md files for ideas (only NOTES.md and Proof.lean).
- Keep NOTES.md concise and structured. Prefer restructuring over appending.
- Only submit working Lean4 proofs. Use `sorry` as a placeholder for incomplete proofs.
- If you are stuck, mark the task as "Stalled" in NOTES.md and suggest alternatives.
- Respond ONLY with a JSON array inside a ```json code block.
  Each element must have "path" (string) and "content" (string) keys.
  You MUST include both NOTES.md and Proof.lean in your response.
"""

# ---------------------------------------------------------------------------
# File helpers
# ---------------------------------------------------------------------------


def read_file(path: Path) -> str:
    """Read a file, returning an empty string if it does not exist."""
    try:
        return path.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError):
        return ""


def write_file(path: Path, content: str) -> None:
    """Write content to a file, creating parent directories as needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def is_safe_path(base_dir: Path, candidate: Path) -> bool:
    """Return True only if `candidate` is inside `base_dir` (prevents path traversal)."""
    try:
        candidate.resolve().relative_to(base_dir.resolve())
        return True
    except ValueError:
        return False


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------


def get_git_log(rel_path: str, n: int = 5) -> str:
    """Return the last n commit messages touching rel_path."""
    try:
        result = subprocess.run(
            ["git", "log", f"-{n}", "--oneline", "--", rel_path],
            capture_output=True,
            text=True,
            cwd=REPO_ROOT,
        )
        return result.stdout.strip()
    except Exception:
        return ""


def was_recently_updated(idea_name: str, minutes: int = 25) -> bool:
    """Return True if the idea folder was committed to within the last `minutes` minutes."""
    try:
        result = subprocess.run(
            [
                "git",
                "log",
                f"--since={minutes} minutes ago",
                "--oneline",
                "--",
                f"candidates/{idea_name}/",
            ],
            capture_output=True,
            text=True,
            cwd=REPO_ROOT,
        )
        return bool(result.stdout.strip())
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Idea selection
# ---------------------------------------------------------------------------

PRIORITY_ORDER: dict[str, int] = {"High": 0, "Medium": 1, "Low": 2}
DEAD_STATUSES: set[str] = {"Dead End", "Archived"}


def get_ideas() -> list[dict]:
    """Parse candidates/README.md and return ideas sorted by priority."""
    content = read_file(REPO_ROOT / "candidates" / "README.md")
    ideas: list[dict] = []
    for line in content.splitlines():
        # Match markdown table rows: | idea-name | Priority | Status |
        m = re.match(
            r"\|\s*([^|]+?)\s*\|\s*(High|Medium|Low)\s*\|\s*([^|]+?)\s*\|",
            line,
        )
        if not m:
            continue
        name, priority, status = m.group(1).strip(), m.group(2).strip(), m.group(3).strip()
        if name.lower() in ("idea name", "---", "---------", "idea-name"):
            continue
        ideas.append({"name": name, "priority": priority, "status": status})
    ideas.sort(key=lambda x: PRIORITY_ORDER.get(x["priority"], 3))
    return ideas


def pick_idea(ideas: list[dict]) -> dict | None:
    """Pick the highest-priority idea that is not a dead end and not recently updated."""
    # First pass: skip recently-updated ideas (locking mechanism)
    for idea in ideas:
        if idea["status"] in DEAD_STATUSES:
            continue
        if not was_recently_updated(idea["name"]):
            return idea
    # Second pass: if all were recently updated, pick the first non-dead one
    for idea in ideas:
        if idea["status"] not in DEAD_STATUSES:
            return idea
    return None


# ---------------------------------------------------------------------------
# Mistral API
# ---------------------------------------------------------------------------


def call_mistral(messages: list[dict], max_tokens: int = 4096) -> str:
    """Call the Mistral chat completions API and return the response text."""
    if not MISTRAL_API_KEY:
        raise ValueError("MISTRAL_VIBE_KEY environment variable is not set.")
    headers = {
        "Authorization": f"Bearer {MISTRAL_API_KEY}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": MISTRAL_MODEL,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": 0.7,
    }
    response = requests.post(MISTRAL_API_URL, headers=headers, json=payload, timeout=180)
    response.raise_for_status()
    return response.json()["choices"][0]["message"]["content"]


# ---------------------------------------------------------------------------
# Response parsing
# ---------------------------------------------------------------------------


def parse_file_updates(response_text: str) -> dict[str, str]:
    """Extract file updates from LLM response (expected: ```json [...] ```)."""
    # Try fenced code block first
    m = re.search(r"```json\s*([\s\S]+?)\s*```", response_text)
    if m:
        try:
            updates = json.loads(m.group(1))
            if isinstance(updates, list):
                return {
                    item["path"]: item["content"]
                    for item in updates
                    if isinstance(item, dict) and "path" in item and "content" in item
                }
        except (json.JSONDecodeError, KeyError):
            pass
    # Fallback: raw JSON array anywhere in the response
    m = re.search(r"\[\s*\{[\s\S]+?\}\s*\]", response_text)
    if m:
        try:
            updates = json.loads(m.group(0))
            if isinstance(updates, list):
                return {
                    item["path"]: item["content"]
                    for item in updates
                    if isinstance(item, dict) and "path" in item and "content" in item
                }
        except (json.JSONDecodeError, KeyError):
            pass
    return {}


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    os.chdir(REPO_ROOT)

    ideas = get_ideas()
    if not ideas:
        print("No ideas found in candidates/README.md — nothing to do.")
        sys.exit(0)

    idea = pick_idea(ideas)
    if idea is None:
        print("No suitable idea found (all are dead ends or recently updated).")
        sys.exit(0)

    idea_name: str = idea["name"]
    idea_path: Path = REPO_ROOT / "candidates" / idea_name

    print(f"Working on idea: {idea_name}  (Priority: {idea['priority']}, Status: {idea['status']})")

    # Gather context
    current_time = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    candidates_readme = read_file(REPO_ROOT / "candidates" / "README.md")
    idea_readme = read_file(idea_path / "README.md")
    idea_notes = read_file(idea_path / "NOTES.md")
    proof_lean = read_file(idea_path / "Proof.lean")
    lib_utils = read_file(REPO_ROOT / "lib" / "utils.lean")
    git_log = get_git_log(f"candidates/{idea_name}/")

    user_message = f"""Current time: {current_time}
You are working on idea: **{idea_name}**

## candidates/README.md (priority list)
{candidates_readme}

## candidates/{idea_name}/README.md (problem statement and hints)
{idea_readme}

## candidates/{idea_name}/NOTES.md (current progress)
{idea_notes}

## candidates/{idea_name}/Proof.lean (current proof)
{proof_lean}

## lib/utils.lean (reusable utilities)
{lib_utils}

## Recent Git Log for this idea
{git_log or "(no recent commits)"}

---

Your task:
1. Review the current state of the proof and notes.
2. Extend or improve the Lean4 proof in candidates/{idea_name}/Proof.lean.
3. Update candidates/{idea_name}/NOTES.md with your progress and next steps.
4. If instructed to refactor code into lib/, update lib/utils.lean accordingly.

Respond ONLY with a JSON array inside a ```json code block.
Each element: {{"path": "...", "content": "..."}}
You MUST include both NOTES.md and Proof.lean.
Only include files you are actually updating (no unnecessary files).

Allowed files:
  - candidates/{idea_name}/NOTES.md
  - candidates/{idea_name}/Proof.lean
  - lib/utils.lean  (only if explicitly refactoring shared code)

Rules:
  - NEVER modify any README.md file.
  - Use `sorry` as a placeholder for incomplete proof steps.
  - Keep NOTES.md concise; restructure rather than append.
  - If stuck, set Status to "Stalled" and suggest alternatives.

Example format:
```json
[
  {{
    "path": "candidates/{idea_name}/NOTES.md",
    "content": "# Progress Notes\\n\\n**Last Updated:** {current_time}\\n..."
  }},
  {{
    "path": "candidates/{idea_name}/Proof.lean",
    "content": "-- Updated Lean4 proof\\n..."
  }}
]
```
"""

    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": user_message},
    ]

    print("Calling Mistral API …")
    response_text = call_mistral(messages)
    print(f"Response received ({len(response_text)} chars).")

    updates = parse_file_updates(response_text)
    if not updates:
        print("ERROR: No file updates could be parsed from the response.")
        print("Response preview:\n", response_text[:800])
        sys.exit(1)

    # Security: allowed paths for researcher
    allowed_prefixes = [
        REPO_ROOT / "candidates" / idea_name,
        REPO_ROOT / "lib",
    ]
    allowed_suffixes_for_idea = {"NOTES.md", "Proof.lean"}

    written = 0
    for rel_path, content in updates.items():
        full_path = (REPO_ROOT / rel_path).resolve()

        # Verify the path is inside the repo
        if not is_safe_path(REPO_ROOT, full_path):
            print(f"SKIP (path traversal): {rel_path}")
            continue

        # Researcher must not touch README.md files
        if Path(rel_path).name == "README.md":
            print(f"SKIP (README.md is read-only for researchers): {rel_path}")
            continue

        # Verify path is under an allowed prefix
        if not any(is_safe_path(prefix, full_path) for prefix in allowed_prefixes):
            print(f"SKIP (not in allowed path): {rel_path}")
            continue

        # Within the idea folder, only NOTES.md and Proof.lean are writable
        if is_safe_path(REPO_ROOT / "candidates" / idea_name, full_path):
            if full_path.name not in allowed_suffixes_for_idea:
                print(f"SKIP (only NOTES.md and Proof.lean allowed in idea folder): {rel_path}")
                continue

        print(f"Writing: {rel_path}")
        write_file(full_path, content)
        written += 1

    print(f"Done. Wrote {written} file(s) for idea: {idea_name}")

    # Emit output for the workflow commit message
    github_output = os.environ.get("GITHUB_OUTPUT", "")
    if github_output:
        with open(github_output, "a", encoding="utf-8") as fh:
            fh.write(f"idea_name={idea_name}\n")


if __name__ == "__main__":
    main()
