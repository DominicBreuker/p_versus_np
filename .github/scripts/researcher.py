#!/usr/bin/env python3
"""
Researcher Agent for the P vs NP Research Project.

This version is intentionally based on the working principles from
`obledev/mistral-action`: it runs the real Mistral Vibe CLI inside the checked
out repository, feeds it a prompt file, and lets the agent work directly in the
workspace instead of calling the chat completions API directly.

Required environment variable:
    MISTRAL_VIBE_KEY or MISTRAL_API_KEY  — Mistral API key

Optional environment variables:
    MISTRAL_MODEL            — Mistral model name
    MISTRAL_MAX_TURNS        — Max Vibe turns (default: 12)
    MISTRAL_MAX_PRICE        — Max Vibe price in dollars
    MISTRAL_TIMEOUT_SECONDS  — Timeout for the Vibe run (default: 1800)
    MISTRAL_VIBE_BIN         — Override path to the `vibe` executable
"""

from __future__ import annotations

import json
import os
import queue
import re
import shutil
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT: Path = Path(__file__).resolve().parent.parent.parent
PROMPT_TEMPLATE_PATH: Path = REPO_ROOT / ".github" / "prompts" / "researcher_vibe.md"
MOCK_VIBE_PATH: Path = REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"
PROMPT_FILENAME = ".mistral-researcher-prompt.md"
PRIORITY_ORDER: dict[str, int] = {"High": 0, "Medium": 1, "Low": 2}
DEAD_STATUSES: set[str] = {"Dead End", "Archived"}
# Vibe emits single-line tagged status messages such as
# `<vibe_stop_event>Turn limit reached</vibe_stop_event>`.
VIBE_TAG_PATTERN = re.compile(r"^<(?P<tag>[a-z_]+)>(?P<message>.*)</(?P=tag)>$")
MISTRAL_MODEL: str = os.environ.get("MISTRAL_MODEL", "").strip()
MISTRAL_MAX_TURNS: str = os.environ.get("MISTRAL_MAX_TURNS", "12").strip()
MISTRAL_MAX_PRICE: str = os.environ.get("MISTRAL_MAX_PRICE", "").strip()
MISTRAL_TIMEOUT_SECONDS: int = int(os.environ.get("MISTRAL_TIMEOUT_SECONDS", "1800"))


def get_mistral_api_key() -> str:
    """Return the configured API key, preferring the researcher-specific variable."""
    if "MISTRAL_VIBE_KEY" in os.environ:
        return os.environ.get("MISTRAL_VIBE_KEY", "").strip()
    return os.environ.get("MISTRAL_API_KEY", "").strip()


MISTRAL_API_KEY: str = get_mistral_api_key()


# ---------------------------------------------------------------------------
# File helpers
# ---------------------------------------------------------------------------


def read_file(path: Path) -> str:
    """Read UTF-8 text from a file and return an empty string on failure."""
    try:
        return path.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError):
        return ""


def write_file(path: Path, content: str) -> None:
    """Write UTF-8 text to a file, creating parent directories as needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def read_text_excerpt(path: Path, limit: int = 4000) -> str:
    """Return a UTF-8 text excerpt for logging discarded edits."""
    try:
        content = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return f"(binary file, {path.stat().st_size} bytes)"
    except OSError as exc:
        return f"(unable to read file: {exc})"

    if len(content) <= limit:
        return content
    return content[:limit] + "\n… (truncated) …"


def is_safe_repo_relative_path(rel_path: str) -> bool:
    """Return True when a repository-relative path resolves inside the repo root."""
    try:
        (REPO_ROOT / rel_path).resolve().relative_to(REPO_ROOT.resolve())
        return True
    except ValueError:
        return False


def ensure_local_git_exclude(entry: str) -> None:
    exclude_file = REPO_ROOT / ".git" / "info" / "exclude"
    existing = read_file(exclude_file)
    existing_lines = set(existing.splitlines())
    additions: list[str] = []
    if "# Local researcher prompt file" not in existing_lines:
        additions.append("# Local researcher prompt file")
    if entry not in existing_lines:
        additions.append(entry)
    if not additions:
        return
    exclude_file.parent.mkdir(parents=True, exist_ok=True)
    with exclude_file.open("a", encoding="utf-8") as fh:
        fh.write("\n" + "\n".join(additions) + "\n")


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------


def run_git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=check,
    )


def get_git_log(rel_path: str, n: int = 5) -> str:
    try:
        return run_git("log", f"-{n}", "--oneline", "--", rel_path, check=False).stdout.strip()
    except Exception:
        return ""


def was_recently_updated(idea_name: str, minutes: int = 25) -> bool:
    try:
        result = run_git(
            "log",
            f"--since={minutes} minutes ago",
            "--oneline",
            "--",
            f"candidates/{idea_name}/",
            check=False,
        )
        return bool(result.stdout.strip())
    except Exception:
        return False


def parse_changed_paths(status_output: str) -> list[str]:
    paths: list[str] = []
    for line in status_output.splitlines():
        if len(line) < 4:
            continue
        path_part = line[3:]
        if " -> " in path_part:
            old_path, new_path = path_part.split(" -> ", 1)
            paths.extend([old_path.strip(), new_path.strip()])
        else:
            paths.append(path_part.strip())
    return paths


def get_changed_paths() -> list[str]:
    result = run_git("status", "--short", check=False)
    return parse_changed_paths(result.stdout)


def get_new_changed_paths(initial_paths: list[str], current_paths: list[str]) -> list[str]:
    initial = set(initial_paths)
    return [path for path in current_paths if path not in initial]


def split_changed_paths(
    changed_paths: list[str],
    allowed_rules: set[str],
) -> tuple[list[str], list[str]]:
    allowed: list[str] = []
    blocked: list[str] = []
    for rel_path in changed_paths:
        normalized = rel_path.strip()
        if not normalized or normalized == PROMPT_FILENAME:
            continue
        if is_path_allowed(normalized, allowed_rules):
            allowed.append(normalized)
        else:
            blocked.append(normalized)
    return allowed, blocked


def is_path_allowed(rel_path: str, allowed_rules: set[str]) -> bool:
    for rule in allowed_rules:
        normalized_rule = rule.strip()
        if not normalized_rule:
            continue
        if normalized_rule.endswith("/"):
            prefix = normalized_rule
            if rel_path.startswith(prefix):
                return True
        elif rel_path == normalized_rule:
            return True
    return False


def revert_path(rel_path: str) -> None:
    if not is_safe_repo_relative_path(rel_path):
        raise ValueError(f"Refusing to touch path outside the repository: {rel_path}")

    restore = run_git("restore", "--source=HEAD", "--staged", "--worktree", "--", rel_path, check=False)
    if restore.returncode == 0:
        return

    full_path = REPO_ROOT / rel_path
    if full_path.is_dir():
        shutil.rmtree(full_path)
    elif full_path.exists():
        full_path.unlink()


def describe_discarded_edit(rel_path: str) -> str:
    header = f"--- discarded edit: {rel_path} ---"
    footer = f"--- end discarded edit: {rel_path} ---"
    diff = run_git("--no-pager", "diff", "--no-ext-diff", "--binary", "--", rel_path, check=False).stdout.strip()
    if diff:
        return f"{header}\n{diff}\n{footer}"

    full_path = REPO_ROOT / rel_path
    if full_path.is_file():
        content = read_text_excerpt(full_path)
        return f"{header}\n{content}\n{footer}"

    if full_path.is_dir():
        parts = [header]
        files = sorted(path for path in full_path.rglob("*") if path.is_file())
        if not files:
            parts.append("(empty directory)")
        for path in files[:20]:
            parts.append(f"# {path.relative_to(REPO_ROOT)}")
            parts.append(read_text_excerpt(path))
        if len(files) > 20:
            parts.append(f"… ({len(files) - 20} additional files omitted) …")
        parts.append(footer)
        return "\n".join(parts)

    return f"{header}\n(path already removed)\n{footer}"


# ---------------------------------------------------------------------------
# Idea selection
# ---------------------------------------------------------------------------


def parse_ideas(content: str) -> list[dict[str, str]]:
    ideas: list[dict[str, str]] = []
    for line in content.splitlines():
        match = re.match(
            r"\|\s*([^|]+?)\s*\|\s*(High|Medium|Low)\s*\|\s*([^|]+?)\s*\|",
            line,
        )
        if not match:
            continue
        name, priority, status = (
            strip_markdown_link(match.group(1).strip()),
            match.group(2).strip(),
            match.group(3).strip(),
        )
        if name.lower() in {"idea name", "---", "---------", "idea-name"}:
            continue
        ideas.append({"name": name, "priority": priority, "status": status})
    ideas.sort(key=lambda item: PRIORITY_ORDER.get(item["priority"], 3))
    return ideas


def strip_markdown_link(value: str) -> str:
    match = re.fullmatch(r"\[([^\]]+)\]\([^)]+\)", value)
    if match:
        return match.group(1).strip()
    return value


def get_ideas() -> list[dict[str, str]]:
    return parse_ideas(read_file(REPO_ROOT / "candidates" / "README.md"))


def pick_idea(ideas: list[dict[str, str]]) -> dict[str, str] | None:
    for idea in ideas:
        if idea["status"] in DEAD_STATUSES:
            continue
        if not was_recently_updated(idea["name"]):
            return idea
    for idea in ideas:
        if idea["status"] not in DEAD_STATUSES:
            return idea
    return None


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------


def allowed_paths_for_idea(idea_name: str) -> set[str]:
    return {
        f"candidates/{idea_name}/",
        "lib/",
    }


def build_prompt(idea_name: str) -> str:
    current_time = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    git_log = get_git_log(f"candidates/{idea_name}/")
    template = read_file(PROMPT_TEMPLATE_PATH)
    if not template:
        raise FileNotFoundError(f"Prompt template not found: {PROMPT_TEMPLATE_PATH}")

    allowed_targets = "\n".join(f"- `{path}**`" if path.endswith("/") else f"- `{path}`" for path in sorted(allowed_paths_for_idea(idea_name)))
    return template.format(
        idea_name=idea_name,
        current_time=current_time,
        git_log=git_log or "(no recent commits)",
        allowed_targets=allowed_targets,
    )


# ---------------------------------------------------------------------------
# Vibe execution
# ---------------------------------------------------------------------------


def find_vibe_executable() -> str:
    configured = os.environ.get("MISTRAL_VIBE_BIN", "").strip()
    if configured:
        return configured
    if MOCK_VIBE_PATH.is_file():
        return str(MOCK_VIBE_PATH)
    executable = shutil.which("vibe")
    if not executable:
        raise RuntimeError("The `vibe` executable was not found on PATH.")
    return executable


@dataclass
class VibeRunResult:
    returncode: int
    stdout: str
    timed_out: bool = False


def format_vibe_streaming_message(payload: dict[str, object]) -> str:
    role = str(payload.get("role") or "assistant")
    tool_calls = payload.get("tool_calls") or []
    content = str(payload.get("content") or "").strip()
    reasoning = str(payload.get("reasoning_content") or "").strip()

    parts: list[str] = []
    if reasoning:
        parts.append(f"reasoning: {reasoning}")
    if isinstance(tool_calls, list) and tool_calls:
        tool_names: list[str] = []
        for item in tool_calls:
            if isinstance(item, dict):
                function = item.get("function") or {}
                if isinstance(function, dict):
                    name = function.get("name")
                    if name:
                        tool_names.append(str(name))
        if tool_names:
            parts.append(f"tool calls: {', '.join(tool_names)}")
    if content:
        parts.append(content)

    if not parts:
        return f"[vibe {role}] {json.dumps(payload, ensure_ascii=False)}"
    return f"[vibe {role}] " + " | ".join(parts)


def format_vibe_output_line(line: str) -> str:
    stripped = line.strip()
    if not stripped:
        return ""

    match = VIBE_TAG_PATTERN.fullmatch(stripped)
    if match:
        formatted = f"[vibe {match.group('tag')}] {match.group('message')}"
        return formatted

    try:
        payload = json.loads(stripped)
    except json.JSONDecodeError:
        formatted = stripped
    else:
        if isinstance(payload, dict):
            formatted = format_vibe_streaming_message(payload)
        else:
            formatted = stripped

    return formatted


def run_vibe(prompt_text: str) -> VibeRunResult:
    prompt_path = REPO_ROOT / PROMPT_FILENAME
    ensure_local_git_exclude(PROMPT_FILENAME)
    write_file(prompt_path, prompt_text)

    # This mirrors the upstream mistral-action approach and relies on Vibe
    # exposing a read_file tool inside programmatic sessions.
    bootstrap_prompt = (
        f"Your full task instructions are in the file `{PROMPT_FILENAME}` "
        f"in the current working directory. Read that file NOW with read_file, "
        f"then follow every instruction in it."
    )

    command = [
        find_vibe_executable(),
        "--prompt",
        bootstrap_prompt,
        "--agent",
        "auto-approve",
        "--workdir",
        str(REPO_ROOT),
        "--trust",
        "--output",
        "streaming",
    ]

    if MISTRAL_MODEL:
        command.extend(["--model", MISTRAL_MODEL])
    if MISTRAL_MAX_TURNS:
        command.extend(["--max-turns", MISTRAL_MAX_TURNS])
    if MISTRAL_MAX_PRICE:
        command.extend(["--max-price", MISTRAL_MAX_PRICE])

    env = os.environ.copy()
    if MISTRAL_API_KEY:
        env["MISTRAL_API_KEY"] = MISTRAL_API_KEY
    env["CI"] = "true"
    env["TERM"] = "dumb"

    try:
        process = subprocess.Popen(
            command,
            cwd=REPO_ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=1,
        )
        if process.stdout is None:
            raise RuntimeError("Failed to capture Vibe output stream.")

        output_lines: list[str] = []
        output_queue: queue.Queue[str | None] = queue.Queue()

        def reader() -> None:
            try:
                for raw_line in process.stdout:
                    output_queue.put(raw_line)
            except Exception as exc:
                output_queue.put(
                    f"<vibe_warning>Output reader failed ({type(exc).__name__}): {exc}</vibe_warning>\n"
                )
            finally:
                process.stdout.close()
                output_queue.put(None)

        reader_thread = threading.Thread(target=reader, daemon=True)
        reader_thread.start()

        timed_out = False
        deadline = time.monotonic() + MISTRAL_TIMEOUT_SECONDS
        while True:
            try:
                raw_line = output_queue.get(timeout=0.2)
            except queue.Empty:
                if process.poll() is None and time.monotonic() > deadline:
                    timed_out = True
                    process.kill()
                    # Keep draining the queue so any buffered final output is logged
                    # before the reader thread emits its sentinel.
                continue

            if raw_line is None:
                break

            output_lines.append(raw_line)
            formatted = format_vibe_output_line(raw_line)
            if formatted:
                print(formatted, flush=True)

        returncode = process.wait()

        return VibeRunResult(
            returncode=returncode,
            stdout="".join(output_lines),
            timed_out=timed_out,
        )
    finally:
        try:
            prompt_path.unlink()
        except FileNotFoundError:
            pass


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def emit_github_output(name: str, value: str) -> None:
    output_file = os.environ.get("GITHUB_OUTPUT", "")
    if not output_file:
        return
    with open(output_file, "a", encoding="utf-8") as fh:
        fh.write(f"{name}={value}\n")


def main() -> None:
    os.chdir(REPO_ROOT)

    initial_changed_paths = get_changed_paths()
    if initial_changed_paths:
        print("Detected existing repository changes; only changes made during this run will be filtered.")
        for rel_path in sorted(set(initial_changed_paths)):
            print(f"  - {rel_path}")

    ideas = get_ideas()
    if not ideas:
        print("No ideas found in candidates/README.md — nothing to do.")
        sys.exit(0)

    idea = pick_idea(ideas)
    if idea is None:
        print("No suitable idea found (all are dead ends or recently updated).")
        sys.exit(0)

    idea_name = idea["name"]
    allowed_paths = allowed_paths_for_idea(idea_name)
    prompt = build_prompt(idea_name)

    print(f"Working on idea: {idea_name}  (Priority: {idea['priority']}, Status: {idea['status']})")
    print("Running Mistral Vibe …")
    result = run_vibe(prompt)

    changed_paths = get_changed_paths()
    new_changed_paths = get_new_changed_paths(initial_changed_paths, changed_paths)
    allowed_changes, blocked_changes = split_changed_paths(new_changed_paths, allowed_paths)

    if blocked_changes:
        print("Discarding blocked changes:")
        for rel_path in sorted(set(blocked_changes)):
            print(describe_discarded_edit(rel_path))
            revert_path(rel_path)
        changed_paths = get_changed_paths()
        new_changed_paths = get_new_changed_paths(initial_changed_paths, changed_paths)
        allowed_changes, blocked_changes = split_changed_paths(new_changed_paths, allowed_paths)

    if blocked_changes:
        print("ERROR: blocked changes remain after cleanup.", file=sys.stderr)
        sys.exit(1)

    if result.timed_out:
        print(
            f"Mistral Vibe timed out after {MISTRAL_TIMEOUT_SECONDS} seconds.",
            file=sys.stderr,
        )
        sys.exit(124)

    if result.returncode != 0:
        print("Mistral Vibe failed.", file=sys.stderr)
        sys.exit(result.returncode)

    if allowed_changes:
        print("Allowed changes:")
        for rel_path in sorted(set(allowed_changes)):
            print(f"  - {rel_path}")
    else:
        print("Mistral Vibe completed without repository changes.")

    emit_github_output("idea_name", idea_name)


if __name__ == "__main__":
    main()
