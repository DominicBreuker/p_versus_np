#!/usr/bin/env python3
from __future__ import annotations

"""Development-only mock for the real Mistral Vibe CLI.

It mirrors the programmatic flags and the session-log/resume behavior used by
the researcher workflow so researcher.py can be tested without a live API key.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import sys
import time
from uuid import uuid4


VERSION = "2.8.1-mock"
PROMPT_FILE_PATTERN = re.compile(r"`([^`]+)`")
SESSION_METADATA_FILENAME = "meta.json"
SESSION_MESSAGES_FILENAME = "messages.jsonl"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Mock Mistral Vibe CLI")
    parser.add_argument("initial_prompt", nargs="?")
    parser.add_argument("-p", "--prompt", nargs="?", const="")
    parser.add_argument("--max-turns", type=int)
    parser.add_argument("--max-price", type=float)
    parser.add_argument("--enabled-tools", action="append")
    parser.add_argument("--output", choices=["text", "json", "streaming"], default="text")
    parser.add_argument("--agent", default="default")
    parser.add_argument("--workdir", type=Path)
    parser.add_argument("--trust", action="store_true")
    parser.add_argument("-v", "--version", action="version", version=f"vibe {VERSION}")
    parser.add_argument("--setup", action="store_true")
    parser.add_argument("--continue", dest="continue_session", action="store_true")
    parser.add_argument("--resume", nargs="?", const=True, default=None)
    return parser.parse_args()


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def get_vibe_home() -> Path:
    vibe_home = os.environ.get("VIBE_HOME", "").strip()
    if vibe_home:
        return Path(vibe_home).expanduser().resolve()
    return Path.home().resolve() / ".vibe"


def get_session_log_dir() -> Path:
    return get_vibe_home() / "logs" / "session"


def generate_session_id() -> str:
    return str(uuid4())


def extract_prompt_path(workdir: Path, bootstrap_prompt: str) -> Path | None:
    matches = PROMPT_FILE_PATTERN.findall(bootstrap_prompt)
    for match in matches:
        candidate = (workdir / match).resolve()
        if candidate.is_file():
            return candidate
    fallback = workdir / ".mistral-researcher-prompt.md"
    if fallback.is_file():
        return fallback
    return None


def read_research_prompt(workdir: Path, bootstrap_prompt: str) -> tuple[str | None, str]:
    """Return `(idea_name, prompt_content)` from the bootstrapped researcher prompt file."""
    prompt_path = extract_prompt_path(workdir, bootstrap_prompt)
    content = ""
    if prompt_path is not None:
        content = prompt_path.read_text(encoding="utf-8")
    else:
        content = bootstrap_prompt
    match = re.search(r"Current target idea:\s*`([^`]+)`", content)
    if match is None:
        match = re.search(r"for `([^`]+)`", content)
    return (match.group(1).strip() if match else None), content


def read_json_file(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json_file(path: Path, content: dict[str, object]) -> None:
    path.write_text(json.dumps(content, indent=2, ensure_ascii=False), encoding="utf-8")


def append_jsonl(path: Path, records: list[dict[str, object]]) -> None:
    with path.open("a", encoding="utf-8") as fh:
        for record in records:
            fh.write(json.dumps(record, ensure_ascii=False) + "\n")


def make_user_message(prompt: str) -> dict[str, object]:
    return {"role": "user", "content": prompt}


def list_valid_sessions() -> list[Path]:
    session_root = get_session_log_dir()
    if not session_root.exists():
        return []
    valid: list[tuple[float, Path]] = []
    for session_dir in session_root.glob("session_*"):
        metadata_path = session_dir / SESSION_METADATA_FILENAME
        messages_path = session_dir / SESSION_MESSAGES_FILENAME
        if not metadata_path.is_file() or not messages_path.is_file():
            continue
        try:
            valid.append((messages_path.stat().st_mtime, session_dir))
        except OSError:
            continue
    valid.sort(key=lambda item: item[0], reverse=True)
    return [path for _, path in valid]


def find_session_dir_by_id(session_id: str) -> Path | None:
    short_id = session_id[:8]
    for session_dir in list_valid_sessions():
        if session_dir.name.endswith(f"_{short_id}"):
            metadata = read_json_file(session_dir / SESSION_METADATA_FILENAME)
            if metadata.get("session_id") == session_id:
                return session_dir
    return None


def create_session_dir(session_id: str) -> Path:
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    session_dir = get_session_log_dir() / f"session_{timestamp}_{session_id[:8]}"
    session_dir.mkdir(parents=True, exist_ok=False)
    write_json_file(session_dir / SESSION_METADATA_FILENAME, {
        "session_id": session_id,
        "start_time": utc_now(),
        "end_time": None,
        "git_commit": None,
        "git_branch": None,
        "parent_session_id": None,
        "environment": {"working_directory": str(Path.cwd().resolve())},
        "username": "mock-vibe",
    })
    return session_dir


def update_session(session_dir: Path, session_id: str, prompt: str, messages: list[dict[str, object]]) -> None:
    append_jsonl(session_dir / SESSION_MESSAGES_FILENAME, [make_user_message(prompt), *messages])
    metadata_path = session_dir / SESSION_METADATA_FILENAME
    metadata = read_json_file(metadata_path)
    metadata["session_id"] = session_id
    metadata["end_time"] = utc_now()
    write_json_file(metadata_path, metadata)


def emit_messages(messages: list[dict[str, object]], output: str) -> None:
    if output == "json":
        json.dump(messages, sys.stdout, ensure_ascii=False)
        sys.stdout.write("\n")
        sys.stdout.flush()
        return

    for message in messages:
        if output == "streaming":
            json.dump(message, sys.stdout, ensure_ascii=False)
            sys.stdout.write("\n")
            sys.stdout.flush()
        else:
            content = str(message.get("content") or "").strip()
            if content:
                print(content, flush=True)
        time.sleep(0.05)


def apply_mock_edits(workdir: Path) -> None:
    instructions = os.environ.get("MOCK_VIBE_WRITE_FILES", "").strip()
    if not instructions:
        return
    edits = json.loads(instructions)
    for edit in edits:
        rel_path = edit["path"]
        mode = edit.get("mode", "write")
        content = edit.get("content", "")
        target = (workdir / rel_path).resolve()
        target.parent.mkdir(parents=True, exist_ok=True)
        if mode == "append" and target.exists():
            with target.open("a", encoding="utf-8") as fh:
                fh.write(content)
        else:
            target.write_text(content, encoding="utf-8")


def resolve_session(args: argparse.Namespace) -> tuple[str, Path, bool]:
    session_log_dir = get_session_log_dir()
    if isinstance(args.resume, str):
        session_dir = find_session_dir_by_id(args.resume)
        if session_dir is None:
            raise FileNotFoundError(f"Session '{args.resume}' not found in {session_log_dir}")
        return args.resume, session_dir, True
    if args.resume is True:
        sessions = list_valid_sessions()
        if not sessions:
            raise FileNotFoundError(f"No previous session found in {session_log_dir}")
        session_dir = sessions[0]
        metadata = read_json_file(session_dir / SESSION_METADATA_FILENAME)
        return str(metadata["session_id"]), session_dir, True
    if args.continue_session:
        sessions = list_valid_sessions()
        if not sessions:
            raise FileNotFoundError(f"No previous session found in {session_log_dir}")
        session_dir = sessions[0]
        metadata = read_json_file(session_dir / SESSION_METADATA_FILENAME)
        return str(metadata["session_id"]), session_dir, True

    session_id = generate_session_id()
    return session_id, create_session_dir(session_id), False


def build_messages(idea_label: str, session_id: str, resumed: bool, agent_name: str) -> list[dict[str, object]]:
    if resumed:
        return [
            {
                "role": "assistant",
                "content": f"Resuming mock Vibe session {session_id} for {idea_label}.",
            },
            {
                "role": "assistant",
                "content": "Continuing from the previous result and next-step ideas.",
            },
            {
                "role": "assistant",
                "content": "Mock Vibe resume pass completed successfully.",
            },
        ]
    return [
        {
            "role": "assistant",
            "content": f"Starting mock Vibe session for {idea_label}.",
        },
        {
            "role": "assistant",
            "content": (
                f"Programmatic mode is active with agent={agent_name}. "
                "I would now inspect the repository instructions and relevant Lean files."
            ),
        },
        {
            "role": "assistant",
            "content": "Mock Vibe completed successfully with follow-up ideas for the next pass.",
        },
    ]


def main() -> int:
    args = parse_args()
    if args.setup:
        print("Mock setup complete.")
        return 0

    workdir = (args.workdir or Path.cwd()).resolve()
    # The real CLI also switches to `--workdir` before running.
    os.chdir(workdir)

    bootstrap_prompt = args.prompt if args.prompt is not None else (args.initial_prompt or "")
    idea_name, _prompt_content = read_research_prompt(workdir, bootstrap_prompt)
    idea_label = idea_name or "unknown-idea"

    try:
        session_id, session_dir, resumed = resolve_session(args)
    except FileNotFoundError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    apply_mock_edits(workdir)
    messages = build_messages(idea_label, session_id, resumed, args.agent)
    update_session(session_dir, session_id, bootstrap_prompt, messages)
    emit_messages(messages, args.output)
    return int(os.environ.get("MOCK_VIBE_EXIT_CODE", "0"))


if __name__ == "__main__":
    sys.exit(main())
