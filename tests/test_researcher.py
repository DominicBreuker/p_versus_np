import contextlib
import importlib.util
import io
import sys
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = REPO_ROOT / ".github" / "scripts" / "researcher.py"

spec = importlib.util.spec_from_file_location("researcher", SCRIPT_PATH)
researcher = importlib.util.module_from_spec(spec)
assert spec.loader is not None
# `dataclass` initialization expects the module object to be present in `sys.modules`
# while the script is being executed.
sys.modules[spec.name] = researcher
spec.loader.exec_module(researcher)


def tearDownModule() -> None:
    sys.modules.pop(spec.name, None)


class ParseIdeasTests(unittest.TestCase):
    def test_parse_ideas_sorts_by_priority(self):
        content = """
| Idea Name | Priority | Status |
|-----------|----------|--------|
| medium-idea | Medium | Active |
| [high-idea](high-idea/) | High | Active |
| low-idea | Low | Archived |
"""
        ideas = researcher.parse_ideas(content)
        self.assertEqual([idea["name"] for idea in ideas], ["high-idea", "medium-idea", "low-idea"])

    def test_get_mistral_api_key_precedence(self):
        with mock.patch.dict(researcher.os.environ, {"MISTRAL_API_KEY": "fallback"}, clear=True):
            self.assertEqual(researcher.get_mistral_api_key(), "fallback")
        with mock.patch.dict(researcher.os.environ, {"MISTRAL_VIBE_KEY": "", "MISTRAL_API_KEY": "fallback"}, clear=True):
            self.assertEqual(researcher.get_mistral_api_key(), "")


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
            "lib/utils.lean",
        ]
        allowed, blocked = researcher.split_changed_paths(changed, {"candidates/foo/", "lib/"})
        self.assertEqual(allowed, ["candidates/foo/Proof.lean", "lib/utils.lean"])
        self.assertEqual(blocked, ["README.md"])

    def test_is_safe_repo_relative_path_rejects_traversal(self):
        self.assertTrue(researcher.is_safe_repo_relative_path("candidates/foo/Proof.lean"))
        self.assertFalse(researcher.is_safe_repo_relative_path("../outside.txt"))

    def test_get_new_changed_paths_only_returns_new_entries(self):
        initial = ["README.md", "lib/utils.lean"]
        current = ["README.md", "lib/utils.lean", "candidates/foo/Proof.lean"]
        self.assertEqual(researcher.get_new_changed_paths(initial, current), ["candidates/foo/Proof.lean"])


class VibeExecutionTests(unittest.TestCase):
    def test_find_vibe_executable_prefers_repo_mock(self):
        with mock.patch.dict(researcher.os.environ, {}, clear=True), \
             mock.patch.object(researcher, "MOCK_VIBE_PATH", REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"):
            self.assertEqual(researcher.find_vibe_executable(), str(REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"))

    def test_format_vibe_output_line_renders_streaming_json(self):
        line = '{"role":"assistant","content":"Hello from mock vibe."}\n'
        self.assertEqual(
            researcher.format_vibe_output_line(line),
            "[vibe assistant] Hello from mock vibe.",
        )

    def test_run_vibe_writes_and_cleans_prompt_file(self):
        prompt_path = REPO_ROOT / researcher.PROMPT_FILENAME
        mock_vibe = REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"
        output = io.StringIO()
        with mock.patch.dict(researcher.os.environ, {"MISTRAL_VIBE_BIN": str(mock_vibe)}, clear=False), \
             contextlib.redirect_stdout(output):
            result = researcher.run_vibe("hello from test")

        self.assertEqual(result.returncode, 0)
        self.assertFalse(prompt_path.exists())
        self.assertIn("[vibe assistant]", output.getvalue())


if __name__ == "__main__":
    unittest.main()
