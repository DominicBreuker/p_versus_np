#!/usr/bin/env python3
"""
Project Leader Agent for the P vs NP Research Project.

Reads the full project state, calls the OpenAI GPT API to:
  - Review idea progress from NOTES.md files and git history
  - Update idea README.md files with new hints/status
  - Update candidates/README.md with revised priorities
  - Update OVERVIEW.md and root README.md
  - Generate new ideas if all existing ones are stalled or dead ends

Required environment variable:
    OPENAI_API_KEY  — OpenAI API key (stored in GitHub secret)

Optional environment variable:
    OPENAI_MODEL    — Model name (default: gpt-4o)
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

OPENAI_API_KEY: str = os.environ.get("OPENAI_API_KEY", "")
OPENAI_MODEL: str = os.environ.get("OPENAI_MODEL", "gpt-4o")
OPENAI_API_URL: str = "https://api.openai.com/v1/chat/completions"

REPO_ROOT: Path = Path(__file__).resolve().parent.parent.parent

SYSTEM_PROMPT: str = """You are the project leader for the "P vs NP" research project. \
You are a senior mathematics researcher with deep expertise in theoretical computer science \
and formal proof systems (Lean4). Your role is to:

1. **Strategic Direction:**
   - Generate new ideas if all existing ones are stalled or dead ends.
   - Update the global OVERVIEW.md with the current state of the project.
   - Update the root README.md with a summary of progress.

2. **Idea Management:**
   - For each idea in candidates/:
     - Review the NOTES.md to assess progress.
     - Update the README.md with new insights, hints, or a status change.
     - If promising: encourage continuation.
     - If stalled: suggest alternative approaches or mark as "Stalled".
     - If a dead end: mark as such.

3. **Priority Updates:**
   - Update candidates/README.md with new priorities.
   - Promote active/promising ideas to "High", demote stalled ones, archive dead ends.

4. **Library Code:**
   - If multiple ideas use similar code, recommend refactoring to lib/ in the idea's README.md.

5. **Success/Dead End Declaration:**
   - If an idea contains a complete proof (no `sorry`), declare success.
   - If all ideas are dead ends, generate at least one new idea.

**Rules:**
- Always keep files concise and well-structured. Prefer restructuring over appending.
- NEVER modify NOTES.md or Proof.lean for EXISTING ideas.
- Only declare success after verifying there are no `sorry` placeholders.
- Respond ONLY with a JSON array inside a ```json code block.
  Each element must have "path" (string) and "content" (string) keys.
"""

# ---------------------------------------------------------------------------
# File helpers
# ---------------------------------------------------------------------------


def read_file(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError):
        return ""


def write_file(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def is_safe_path(base_dir: Path, candidate: Path) -> bool:
    try:
        candidate.resolve().relative_to(base_dir.resolve())
        return True
    except ValueError:
        return False


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------


def get_git_log(rel_path: str, n: int = 10) -> str:
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


# ---------------------------------------------------------------------------
# OpenAI API
# ---------------------------------------------------------------------------


def call_openai(messages: list[dict], max_tokens: int = 4096) -> str:
    if not OPENAI_API_KEY:
        raise ValueError("OPENAI_API_KEY environment variable is not set.")
    headers = {
        "Authorization": f"Bearer {OPENAI_API_KEY}",
        "Content-Type": "application/json",
    }
    payload = {
        "model": OPENAI_MODEL,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": 0.7,
    }
    response = requests.post(OPENAI_API_URL, headers=headers, json=payload, timeout=240)
    response.raise_for_status()
    return response.json()["choices"][0]["message"]["content"]


# ---------------------------------------------------------------------------
# Response parsing
# ---------------------------------------------------------------------------


def parse_file_updates(response_text: str) -> dict[str, str]:
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

    current_time = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")

    # Gather project state
    root_readme = read_file(REPO_ROOT / "README.md")
    overview = read_file(REPO_ROOT / "OVERVIEW.md")
    candidates_readme = read_file(REPO_ROOT / "candidates" / "README.md")

    # Collect all idea data
    candidates_dir = REPO_ROOT / "candidates"
    idea_dirs = sorted(
        [d for d in candidates_dir.iterdir() if d.is_dir()],
        key=lambda d: d.name,
    ) if candidates_dir.exists() else []

    ideas_context_parts: list[str] = []
    for idea_dir in idea_dirs:
        idea_name = idea_dir.name
        readme = read_file(idea_dir / "README.md")
        notes = read_file(idea_dir / "NOTES.md")
        proof = read_file(idea_dir / "Proof.lean")
        git_log = get_git_log(f"candidates/{idea_name}/")
        has_sorry = "sorry" in proof

        ideas_context_parts.append(
            f"### {idea_name}\n"
            f"**Proof has `sorry` placeholders:** {has_sorry}\n\n"
            f"#### README.md\n{readme}\n\n"
            f"#### NOTES.md\n{notes}\n\n"
            f"#### Recent Git Log\n{git_log or '(no recent commits)'}\n"
        )

    ideas_context = "\n---\n".join(ideas_context_parts) if ideas_context_parts else "(no ideas yet)"

    user_message = f"""Current time: {current_time}

## Root README.md
{root_readme}

## OVERVIEW.md
{overview}

## candidates/README.md (priority list)
{candidates_readme}

## Ideas Status
{ideas_context}

---

Your tasks:
1. Review ALL ideas' NOTES.md and git logs to assess progress.
2. Update each existing idea's README.md with new insights, hints, or status changes.
3. Update candidates/README.md with new priorities (High/Medium/Low) and statuses.
4. Update OVERVIEW.md with the current project state.
5. Update root README.md with a progress summary and updated status.
6. If ALL ideas are dead ends or stalled with no progress, generate at least one NEW idea.
   For a new idea, include:
   - candidates/<new-idea-name>/README.md
   - candidates/<new-idea-name>/NOTES.md  (initial stub)
   - candidates/<new-idea-name>/Proof.lean (initial stub with sorry)

Respond ONLY with a JSON array inside a ```json code block.
Each element: {{"path": "...", "content": "..."}}

Allowed files to write:
  - README.md  (root)
  - OVERVIEW.md
  - candidates/README.md
  - candidates/<idea-name>/README.md  (any existing or new idea)
  - candidates/<new-idea-name>/NOTES.md   (ONLY for brand-new ideas)
  - candidates/<new-idea-name>/Proof.lean (ONLY for brand-new ideas)
  - lib/utils.lean  (only for library recommendations)

Rules:
  - NEVER modify NOTES.md or Proof.lean for EXISTING ideas.
  - Only declare success if a proof file has NO `sorry` placeholders.
  - Keep all files concise. Prefer restructuring over appending.
"""

    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": user_message},
    ]

    print("Calling OpenAI API …")
    response_text = call_openai(messages)
    print(f"Response received ({len(response_text)} chars).")

    updates = parse_file_updates(response_text)
    if not updates:
        print("ERROR: No file updates could be parsed from the response.")
        print("Response preview:\n", response_text[:800])
        sys.exit(1)

    # Identify existing idea directories (for write-protection of NOTES/Proof)
    existing_idea_names: set[str] = {d.name for d in idea_dirs}

    written = 0
    for rel_path, content in updates.items():
        full_path = (REPO_ROOT / rel_path).resolve()

        # Verify the path is inside the repo
        if not is_safe_path(REPO_ROOT, full_path):
            print(f"SKIP (path traversal): {rel_path}")
            continue

        parts = Path(rel_path).parts

        # Root-level markdown files
        if len(parts) == 1 and rel_path in {"README.md", "OVERVIEW.md"}:
            pass  # allowed

        # candidates/README.md
        elif rel_path == "candidates/README.md":
            pass  # allowed

        # candidates/<idea>/README.md — always allowed (new or existing)
        elif (
            len(parts) == 3
            and parts[0] == "candidates"
            and parts[2] == "README.md"
        ):
            pass  # allowed

        # candidates/<idea>/NOTES.md or Proof.lean — only for NEW ideas
        elif (
            len(parts) == 3
            and parts[0] == "candidates"
            and parts[2] in {"NOTES.md", "Proof.lean"}
        ):
            idea_name = parts[1]
            if idea_name in existing_idea_names:
                print(f"SKIP (cannot modify {parts[2]} of existing idea): {rel_path}")
                continue
            # New idea — allowed

        # lib/ files
        elif len(parts) >= 2 and parts[0] == "lib":
            pass  # allowed

        else:
            print(f"SKIP (not in allowed paths): {rel_path}")
            continue

        print(f"Writing: {rel_path}")
        write_file(full_path, content)
        written += 1

    print(f"Done. Wrote {written} file(s).")


if __name__ == "__main__":
    main()
