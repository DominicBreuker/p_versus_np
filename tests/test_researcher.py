import importlib.util
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path("/home/runner/work/p_versus_np/p_versus_np")
SCRIPT_PATH = REPO_ROOT / ".github" / "scripts" / "researcher.py"

spec = importlib.util.spec_from_file_location("researcher", SCRIPT_PATH)
researcher = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(researcher)


class ParseIdeasTests(unittest.TestCase):
    def test_parse_ideas_sorts_by_priority(self):
        content = """
| Idea Name | Priority | Status |
|-----------|----------|--------|
| medium-idea | Medium | Active |
| high-idea | High | Active |
| low-idea | Low | Archived |
"""
        ideas = researcher.parse_ideas(content)
        self.assertEqual([idea["name"] for idea in ideas], ["high-idea", "medium-idea", "low-idea"])


class ChangedPathTests(unittest.TestCase):
    def test_parse_changed_paths_handles_standard_and_renamed_paths(self):
        status_output = " M candidates/foo/Proof.lean\nR  candidates/foo/Old.lean -> candidates/foo/New.lean\n?? lib/utils.lean\n"
        self.assertEqual(
            researcher.parse_changed_paths(status_output),
            [
                "candidates/foo/Proof.lean",
                "candidates/foo/Old.lean",
                "candidates/foo/New.lean",
                "lib/utils.lean",
            ],
        )

    def test_split_changed_paths_filters_prompt_file(self):
        changed = [
            researcher.PROMPT_FILENAME,
            "candidates/foo/Proof.lean",
            "README.md",
        ]
        allowed, blocked = researcher.split_changed_paths(changed, {"candidates/foo/Proof.lean"})
        self.assertEqual(allowed, ["candidates/foo/Proof.lean"])
        self.assertEqual(blocked, ["README.md"])


class VibeExecutionTests(unittest.TestCase):
    def test_run_vibe_writes_and_cleans_prompt_file(self):
        prompt_path = REPO_ROOT / researcher.PROMPT_FILENAME
        completed = subprocess.CompletedProcess(args=["vibe"], returncode=0, stdout="ok", stderr="")

        with mock.patch.object(researcher, "find_vibe_executable", return_value="/usr/bin/vibe"), \
             mock.patch.object(researcher.subprocess, "run", return_value=completed) as mocked_run:
            result = researcher.run_vibe("hello from test")

        self.assertEqual(result.returncode, 0)
        self.assertFalse(prompt_path.exists())
        called_command = mocked_run.call_args.kwargs["args"] if "args" in mocked_run.call_args.kwargs else mocked_run.call_args.args[0]
        self.assertIn("--prompt", called_command)
        self.assertIn("--workdir", called_command)


if __name__ == "__main__":
    unittest.main()
