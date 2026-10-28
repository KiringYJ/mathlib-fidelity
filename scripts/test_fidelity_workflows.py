"""Regression tests for the active workflow admission boundary."""

from pathlib import Path
import tempfile
import unittest

from check_fidelity_workflows import WORKFLOWS, check_workflows


class WorkflowInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repository = Path(self.temporary.name)
        self.workflows = self.repository / ".github" / "workflows"
        self.workflows.mkdir(parents=True)
        for name in WORKFLOWS:
            (self.workflows / name).touch()

    def test_reviewed_inventory_passes(self):
        self.assertEqual(check_workflows(self.repository), [])

    def test_upstream_additions_fail_for_both_extensions(self):
        for extension in ("yml", "yaml", "YML"):
            with self.subTest(extension=extension):
                added = self.workflows / f"new-upstream-bot.{extension}"
                added.touch()
                self.assertEqual(
                    check_workflows(self.repository),
                    [f"Unreviewed active workflow: {added.name}"],
                )
                added.unlink()

    def test_removing_a_required_check_fails(self):
        (self.workflows / "fidelity-ci.yml").unlink()
        self.assertEqual(
            check_workflows(self.repository),
            ["Missing required workflow: fidelity-ci.yml"],
        )

    def test_archived_workflows_are_excluded_from_inventory(self):
        archive = self.repository / ".github" / "upstream-workflows"
        archive.mkdir()
        (archive / "build_fork.yml").write_text("on: pull_request_target\n")
        self.assertEqual(check_workflows(self.repository), [])


if __name__ == "__main__":
    unittest.main()
