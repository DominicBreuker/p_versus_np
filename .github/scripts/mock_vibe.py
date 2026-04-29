#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path


VERSION = "2.8.1-mock"
PROMPT_FILE_PATTERN = re.compile(r"`([^`]+)`")


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
    parser.add_argument("--resume", nargs="?")
    return parser.parse_args()


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
    prompt_path = extract_prompt_path(workdir, bootstrap_prompt)
    if prompt_path is None:
        return None, ""
    content = prompt_path.read_text(encoding="utf-8")
    match = re.search(r"Current target idea:\s*`([^`]+)`", content)
    return (match.group(1).strip() if match else None), content


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


def main() -> int:
    args = parse_args()
    if args.setup:
        print("Mock setup complete.")
        return 0

    workdir = (args.workdir or Path.cwd()).resolve()
    bootstrap_prompt = args.prompt if args.prompt is not None else (args.initial_prompt or "")
    idea_name, _prompt_content = read_research_prompt(workdir, bootstrap_prompt)
    idea_label = idea_name or "unknown-idea"

    apply_mock_edits(workdir)

    messages = [
        {
            "role": "assistant",
            "content": f"Starting mock Vibe session for {idea_label}.",
        },
        {
            "role": "assistant",
            "content": (
                f"Programmatic mode is active with agent={args.agent}. "
                "I would now inspect the repository instructions and relevant Lean files."
            ),
        },
        {
            "role": "assistant",
            "content": "Mock Vibe completed successfully.",
        },
    ]
    emit_messages(messages, args.output)
    return int(os.environ.get("MOCK_VIBE_EXIT_CODE", "0"))


if __name__ == "__main__":
    raise SystemExit(main())
