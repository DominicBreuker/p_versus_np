import contextlib
import importlib.util
import io
import sys
import tempfile
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


class ParseTargetsTests(unittest.TestCase):
    def test_parse_targets_sorts_by_descending_numeric_priority(self):
        content = """
| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [problem-b](problem-b/) | [approach-b](problem-b/approach-b/) | 25 | Active | Supports main route |
| [problem-a](problem-a/) | [approach-a](problem-a/approach-a/) | 100 | Active | Main proof track |
| [problem-c](problem-c/) | [approach-c](problem-c/approach-c/) | 10 | Archived | Retired |
"""
        targets = researcher.parse_targets(content)
        self.assertEqual(
            [(target["problem"], target["approach"]) for target in targets],
            [("problem-a", "approach-a"), ("problem-b", "approach-b"), ("problem-c", "approach-c")],
        )

    def test_get_mistral_api_key_precedence(self):
        with mock.patch.dict(researcher.os.environ, {"MISTRAL_API_KEY": "fallback"}, clear=True):
            self.assertEqual(researcher.get_mistral_api_key(), "fallback")
        with mock.patch.dict(researcher.os.environ, {"MISTRAL_VIBE_KEY": "", "MISTRAL_API_KEY": "fallback"}, clear=True):
            self.assertEqual(researcher.get_mistral_api_key(), "")

    def test_pick_target_uses_priority_weights(self):
        targets = [
            {"problem": "p1", "approach": "a1", "priority": "90", "priority_value": 90.0, "status": "Active"},
            {"problem": "p2", "approach": "a2", "priority": "10", "priority_value": 10.0, "status": "Active"},
        ]
        with mock.patch.object(researcher.random, "choices", return_value=[targets[0]]) as choices:
            chosen = researcher.pick_target(targets)
        self.assertEqual(chosen, targets[0])
        choices.assert_called_once_with(targets, weights=[90.0, 10.0], k=1)


class ChangedPathTests(unittest.TestCase):
    def test_parse_changed_paths_handles_standard_and_renamed_paths(self):
        status_output = " M proofs/problem/foo/Proof.lean\nR  proofs/problem/foo/Old.lean -> proofs/problem/foo/New.lean\n?? lib/utils.lean\n"
        self.assertEqual(
            researcher.parse_changed_paths(status_output),
            [
                "proofs/problem/foo/Proof.lean",
                "proofs/problem/foo/Old.lean",
                "proofs/problem/foo/New.lean",
                "lib/utils.lean",
            ],
        )

    def test_split_changed_paths_filters_prompt_file(self):
        changed = [
            researcher.PROMPT_FILENAME,
            "proofs/problem/foo/Proof.lean",
            "README.md",
            "lib/utils.lean",
        ]
        allowed, blocked = researcher.split_changed_paths(changed, {"proofs/problem/foo/", "lib/"})
        self.assertEqual(allowed, ["proofs/problem/foo/Proof.lean", "lib/utils.lean"])
        self.assertEqual(blocked, ["README.md"])

    def test_is_safe_repo_relative_path_rejects_traversal(self):
        self.assertTrue(researcher.is_safe_repo_relative_path("proofs/problem/foo/Proof.lean"))
        self.assertFalse(researcher.is_safe_repo_relative_path("../outside.txt"))

    def test_get_new_changed_paths_only_returns_new_entries(self):
        initial = ["README.md", "lib/utils.lean"]
        current = ["README.md", "lib/utils.lean", "proofs/problem/foo/Proof.lean"]
        self.assertEqual(researcher.get_new_changed_paths(initial, current), ["proofs/problem/foo/Proof.lean"])


class VibeExecutionTests(unittest.TestCase):
    def test_find_vibe_executable_prefers_explicit_env_override(self):
        mock_vibe = REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"
        with mock.patch.dict(researcher.os.environ, {"MISTRAL_VIBE_BIN": str(mock_vibe)}, clear=True):
            self.assertEqual(researcher.find_vibe_executable(), str(mock_vibe))

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
        with tempfile.TemporaryDirectory() as tmpdir, \
             mock.patch.dict(
                 researcher.os.environ,
                 {"MISTRAL_VIBE_BIN": str(mock_vibe), "VIBE_HOME": tmpdir},
                 clear=False,
             ), \
             contextlib.redirect_stdout(output):
            result = researcher.run_vibe("hello from test")

        self.assertEqual(result.returncode, 0)
        self.assertFalse(prompt_path.exists())
        self.assertIn("[vibe assistant]", output.getvalue())

    def test_bind_latest_session_to_explicit_id_supports_resume(self):
        mock_vibe = REPO_ROOT / ".github" / "scripts" / "mock_vibe.py"
        explicit_session_id = "12345678-1234-1234-1234-123456789abc"

        with tempfile.TemporaryDirectory() as tmpdir:
            with mock.patch.dict(
                researcher.os.environ,
                {"MISTRAL_VIBE_BIN": str(mock_vibe), "VIBE_HOME": tmpdir},
                clear=False,
            ):
                first = researcher.run_vibe("hello from test")
                self.assertEqual(first.returncode, 0)

                session_dir = researcher.bind_latest_session_to_explicit_id(explicit_session_id)
                self.assertTrue(session_dir.name.endswith("_12345678"))

                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    second = researcher.run_vibe(
                        "resume now",
                        resume_session_id=explicit_session_id,
                        bootstrap_from_file=False,
                    )

                self.assertEqual(second.returncode, 0)
                self.assertIn("Resuming mock Vibe session", output.getvalue())

    def test_append_failure_note_creates_technical_interruptions_section(self):
        notes_path = REPO_ROOT / "proofs" / "p_versus_np" / "circuit-lower-bounds" / "NOTES.md"
        original = notes_path.read_text(encoding="utf-8")
        try:
            notes_path.write_text("# Progress Notes\n", encoding="utf-8")
            researcher.append_failure_note("p_versus_np", "circuit-lower-bounds", "mock timeout")
            updated = notes_path.read_text(encoding="utf-8")
            self.assertIn("## Technical Interruptions", updated)
            self.assertIn("mock timeout", updated)
        finally:
            notes_path.write_text(original, encoding="utf-8")


if __name__ == "__main__":
    unittest.main()
