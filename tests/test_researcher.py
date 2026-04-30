import contextlib
import importlib.util
import io
import subprocess
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

    def test_parse_targets_ignores_malformed_and_header_rows(self):
        content = """
Problem | Approach | Priority | Status | Relationships
| Problem | Approach | Priority | Status | Relationships |
|---------|----------|----------|--------|---------------|
| [problem-a](problem-a/) | [approach-a](problem-a/approach-a/) | 100 | Active | Main proof track |
"""
        targets = researcher.parse_targets(content)
        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["problem"], "problem-a")
        self.assertEqual(targets[0]["relationships"], "Main proof track")

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

    def test_parse_args_accepts_run_count_and_overall_timeout(self):
        args = researcher.parse_args(["--run-count", "5", "--overall-timeout-minutes", "12.5"])
        self.assertEqual(args.run_count, 5)
        self.assertEqual(args.overall_timeout_minutes, 12.5)

    def test_parse_args_rejects_non_positive_run_count(self):
        with self.assertRaises(SystemExit):
            researcher.parse_args(["--run-count", "0"])


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

    def test_main_stops_starting_new_runs_after_overall_timeout(self):
        target = {
            "problem": "p_versus_np",
            "approach": "circuit-lower-bounds",
            "priority": "90",
            "priority_value": 90.0,
            "status": "Active",
        }
        with mock.patch.object(researcher, "find_vibe_executable", return_value="mock-vibe"), \
             mock.patch.object(researcher, "is_mock_vibe_executable", return_value=True), \
             mock.patch.object(researcher, "get_changed_paths", return_value=[]), \
             mock.patch.object(researcher, "get_targets", return_value=[target]), \
             mock.patch.object(researcher, "pick_target", return_value=target), \
             mock.patch.object(researcher, "build_prompt", return_value="mock prompt"), \
             mock.patch.object(researcher, "resolve_session_id", return_value="session-123"), \
             mock.patch.object(
                 researcher,
                 "run_vibe",
                 return_value=researcher.VibeRunResult(returncode=0, stdout=""),
             ) as run_vibe, \
             mock.patch.object(researcher, "bind_latest_session_to_explicit_id"), \
             mock.patch.object(researcher, "finalize_changes", return_value=([], [])), \
             mock.patch.object(
                 researcher,
                 "commit_and_push_run",
                 return_value=researcher.GitPushResult(branch_name="main"),
             ) as commit_and_push_run, \
             mock.patch.object(researcher, "emit_github_output") as emit_output, \
             mock.patch.object(researcher.time, "monotonic", side_effect=[0.0, 0.0, 61.0]), \
             mock.patch.object(sys, "argv", ["researcher.py", "--run-count", "3", "--overall-timeout-minutes", "1"]):
            researcher.main()

        self.assertEqual(run_vibe.call_count, 2)
        self.assertEqual(commit_and_push_run.call_count, 2)
        outputs = {call.args[0]: call.args[1] for call in emit_output.call_args_list}
        self.assertEqual(outputs["requested_run_count"], "3")
        self.assertEqual(outputs["completed_run_count"], "2")
        self.assertEqual(outputs["overall_timeout_reached"], "true")


class GitPushTests(unittest.TestCase):
    def git(self, repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            text=True,
            capture_output=True,
            check=check,
        )

    def write_text(self, path: Path, content: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def configure_repo(self, repo: Path, name: str) -> None:
        self.git(repo, "config", "user.name", name)
        self.git(repo, "config", "user.email", f"{name.lower().replace(' ', '-')}@example.com")

    def make_remote_pair(self) -> tuple[tempfile.TemporaryDirectory, Path, Path, Path]:
        tmpdir = tempfile.TemporaryDirectory()
        root = Path(tmpdir.name)
        remote = root / "remote.git"
        primary = root / "primary"
        peer = root / "peer"

        subprocess.run(["git", "init", "--bare", str(remote)], check=True, capture_output=True, text=True)
        subprocess.run(["git", "clone", str(remote), str(primary)], check=True, capture_output=True, text=True)
        self.git(primary, "checkout", "-b", "main")
        self.configure_repo(primary, "Primary Tester")
        self.write_text(primary / "shared.txt", "base\n")
        self.git(primary, "add", "shared.txt")
        self.git(primary, "commit", "-m", "Initial commit")
        self.git(primary, "push", "--set-upstream", "origin", "main")
        subprocess.run(
            ["git", "symbolic-ref", "HEAD", "refs/heads/main"],
            cwd=remote,
            check=True,
            capture_output=True,
            text=True,
        )

        subprocess.run(["git", "clone", str(remote), str(peer)], check=True, capture_output=True, text=True)
        self.configure_repo(peer, "Peer Tester")
        return tmpdir, remote, primary, peer

    def test_commit_and_push_run_rebases_clean_remote_updates(self):
        tmpdir, _remote, primary, peer = self.make_remote_pair()
        self.addCleanup(tmpdir.cleanup)

        self.write_text(peer / "peer.txt", "from peer\n")
        self.git(peer, "add", "peer.txt")
        self.git(peer, "commit", "-m", "Peer change")
        self.git(peer, "push", "origin", "main")

        self.write_text(primary / "primary.txt", "from primary\n")
        with mock.patch.object(researcher, "REPO_ROOT", primary), \
             mock.patch.object(researcher, "MISTRAL_AGENT", "lean"):
            result = researcher.commit_and_push_run(
                commit_message="Researcher update: run 1/2",
                target_label="p_versus_np/circuit-lower-bounds",
                run_index=1,
            )

        self.assertFalse(result.used_fallback_branch)
        self.assertEqual(result.branch_name, "main")
        self.git(primary, "fetch", "origin")
        self.assertIn("Peer change", self.git(primary, "log", "origin/main", "--oneline").stdout)
        self.assertIn("Researcher update: run 1/2", self.git(primary, "log", "origin/main", "--oneline").stdout)

    def test_commit_and_push_run_uses_fallback_branch_on_rebase_conflict(self):
        tmpdir, _remote, primary, peer = self.make_remote_pair()
        self.addCleanup(tmpdir.cleanup)

        self.write_text(peer / "shared.txt", "peer version\n")
        self.git(peer, "add", "shared.txt")
        self.git(peer, "commit", "-m", "Conflicting peer change")
        self.git(peer, "push", "origin", "main")

        self.write_text(primary / "shared.txt", "primary version\n")
        with mock.patch.object(researcher, "REPO_ROOT", primary), \
             mock.patch.object(researcher, "MISTRAL_AGENT", "lean"):
            result = researcher.commit_and_push_run(
                commit_message="Researcher update: run 2/2",
                target_label="p_versus_np/circuit-lower-bounds",
                run_index=2,
            )

        self.assertTrue(result.used_fallback_branch)
        self.assertTrue(result.branch_name.startswith("researcher-backup/"))
        self.git(primary, "fetch", "origin")
        remote_branches = self.git(primary, "branch", "-r").stdout
        self.assertIn(f"origin/{result.branch_name}", remote_branches)
        self.assertEqual(self.git(primary, "rev-parse", "--abbrev-ref", "HEAD").stdout.strip(), result.branch_name)


if __name__ == "__main__":
    unittest.main()
