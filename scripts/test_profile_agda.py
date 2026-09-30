"""Checks for bounded profiling, immutable sources, and owned-process timeouts."""

from pathlib import Path
import sys
import tempfile
import unittest

from check_agda import ROOT
from profile_agda import has_hash, run_command, scope, sha256, snapshot


def graph(edges):
    return {name: (Path(name), set(imports), "hash") for name, imports in edges.items()}


class ScopeTests(unittest.TestCase):
    def test_selected_dependencies_run_before_consumers(self):
        ordered, entries = scope(graph({"SCT.A": ["SCT.B"], "SCT.B": ["SCT.C"],
                                        "SCT.C": []}), ["SCT.A", "SCT.B", "SCT.A"])
        self.assertEqual(ordered, ["SCT.C", "SCT.B", "SCT.A"])
        self.assertEqual(entries, ["SCT.B", "SCT.A"])

    def test_rejects_full_aggregates(self):
        for name in ["SCT.Everything", "SCT.VolumeI.Chapter01.Everything", "SCT.WebEdition"]:
            with self.assertRaisesRegex(ValueError, "aggregates"):
                scope(graph({name: []}), [name])

    def test_rejects_transitive_aggregate(self):
        with self.assertRaisesRegex(ValueError, "aggregate"):
            scope(graph({"SCT.A": ["SCT.Everything"], "SCT.Everything": []}), ["SCT.A"])

    def test_rejects_deferred_transitive_branch(self):
        slow = "SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyUncurrying"
        with self.assertRaisesRegex(ValueError, "deferred branch"):
            scope(graph({"SCT.A": [slow], slow: []}), ["SCT.A"])

    def test_reports_cycle_and_missing_import(self):
        with self.assertRaisesRegex(ValueError, "Import cycle"):
            scope(graph({"SCT.A": ["SCT.B"], "SCT.B": ["SCT.A"]}), ["SCT.A"])
        with self.assertRaisesRegex(ValueError, "Missing module"):
            scope(graph({"SCT.A": ["SCT.B"]}), ["SCT.A"])

    def test_requires_a_small_explicit_scope(self):
        with self.assertRaises(ValueError):
            scope({}, [])
        with self.assertRaises(ValueError):
            scope({}, [f"SCT.A{i}" for i in range(9)])


class FilesAndProcessTests(unittest.TestCase):
    def setUp(self):
        self.parent = (ROOT / "_build/profile-tests").resolve()
        self.parent.mkdir(parents=True, exist_ok=True)
        self.storage = tempfile.TemporaryDirectory(prefix="owned-", dir=self.parent)
        self.root = Path(self.storage.name).resolve()
        self.assertTrue(self.root.is_relative_to(self.parent))

    def tearDown(self):
        # Only the generated, individually owned test directory is removed.
        self.assertTrue(self.root.resolve().is_relative_to(self.parent))
        self.assertNotEqual(self.root.resolve(), self.parent)
        self.storage.cleanup()

    def fixture(self):
        source, cache = self.root / "source", self.root / "cache"
        (source / "SCT").mkdir(parents=True)
        (cache / "SCT").mkdir(parents=True)
        modules = {}
        for name in ["A", "B"]:
            p = source / "SCT" / (name + ".lagda.md")
            p.write_text("# Example\n\n```agda\nmodule SCT." + name + " where\n```\n", encoding="utf-8")
            (cache / "SCT" / (name + ".agdai")).write_bytes(b"original interface " + name.encode())
            modules["SCT." + name] = (p, {"SCT.B"} if name == "A" else set(), sha256(p))
        return modules, source, cache

    def test_snapshot_omits_only_entry_interfaces_and_leaves_originals_unchanged(self):
        modules, source, cache = self.fixture()
        before = {p: p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        dest = self.root / "snapshot"
        manifest = snapshot(modules, ["SCT.B", "SCT.A"], ["SCT.A"], source, cache, dest)
        self.assertFalse((dest / "SCT/A.agdai").exists())
        self.assertEqual((dest / "SCT/B.agdai").read_bytes(), (cache / "SCT/B.agdai").read_bytes())
        self.assertEqual((dest / "SCT/A.lagda.md").read_bytes(), (source / "SCT/A.lagda.md").read_bytes())
        self.assertNotIn("interface_sha256", manifest["SCT.A"])
        self.assertIn("interface_sha256", manifest["SCT.B"])
        for p, contents in before.items():
            self.assertEqual(p.read_bytes(), contents)

    def test_snapshot_rejects_sources_changed_after_planning(self):
        modules, source, cache = self.fixture()
        (source / "SCT/A.lagda.md").write_text("changed", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Source changed"):
            snapshot(modules, ["SCT.B", "SCT.A"], ["SCT.A"], source, cache, self.root / "snapshot")

    def test_nonzero_status_and_partial_statistics_are_recorded(self):
        code = "print('Checking SCT.Example'); print(' 1,234 bytes allocated in the heap'); raise SystemExit(42)"
        row = run_command([sys.executable, "-c", code], self.root / "failure.log", 5, self.root)
        self.assertEqual(row["status"], 42)
        self.assertEqual(row["checked_modules"], ["SCT.Example"])
        self.assertEqual(row["allocated_bytes"], 1234)
        self.assertIsNone(row["maximum_residency_bytes"])

    def test_launch_failure_is_reported(self):
        row = run_command([str(self.root / "missing-executable")], self.root / "launch.log", 5, self.root)
        self.assertEqual(row["status"], "error")
        self.assertIn("error", row)
        self.assertFalse(row["checked_modules"])

    def test_missing_source_is_drift(self):
        self.assertFalse(has_hash(self.root / "missing-source", "hash"))

    def test_timeout_stops_owned_child_and_keeps_output(self):
        code = "import time; print('Checking SCT.Waiting', flush=True); time.sleep(30)"
        log = self.root / "timeout.log"
        row = run_command([sys.executable, "-c", code], log, 0.5, self.root)
        self.assertEqual(row["status"], "timeout")
        self.assertLess(row["seconds"], 5)
        self.assertIn("Checking SCT.Waiting", log.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
