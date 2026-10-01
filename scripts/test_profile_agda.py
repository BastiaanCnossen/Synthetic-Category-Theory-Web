"""Checks for bounded profiling, immutable sources, and owned-process timeouts."""

from pathlib import Path
import sys
import json
import zipfile
import tempfile
import unittest
from unittest.mock import patch
import profile_agda

from check_agda import ROOT
from profile_agda import (archive_run, has_hash, run_command, scope, seed_interfaces,
                          sha256, snapshot, snapshot_modules)


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

    def test_seed_requires_matching_source_and_interface_hashes(self):
        modules, source, cache = self.fixture()
        alternative = self.root / "seed.agdai"
        alternative.write_bytes(b"seeded B")
        seed = {"SCT.B": (alternative, modules["SCT.B"][2], sha256(alternative))}
        dest = self.root / "seeded"
        snapshot(modules, ["SCT.B", "SCT.A"], ["SCT.A"], source, cache, dest, seed)
        self.assertEqual((dest / "SCT/B.agdai").read_bytes(), b"seeded B")
        seed["SCT.B"] = (alternative, "wrong source", sha256(alternative))
        dest = self.root / "unseeded"
        snapshot(modules, ["SCT.B"], [], source, cache, dest, seed)
        self.assertEqual((dest / "SCT/B.agdai").read_bytes(), b"original interface B")

    def test_snapshot_graph_uses_changed_imports_and_rejects_deferred_branch(self):
        _, source, _ = self.fixture()
        slow = "SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyUncurrying"
        (source / "SCT/A.lagda.md").write_text("```agda\nmodule SCT.A where\nimport " + slow + "\n```\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Missing module"):
            scope(snapshot_modules(source), ["SCT.A"])
        slow_path = source / Path(*slow.split(".")).with_suffix(".agda")
        slow_path.parent.mkdir(parents=True)
        slow_path.write_text("module " + slow + " where\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "deferred branch"):
            scope(snapshot_modules(source), ["SCT.A"])

    def test_archive_preserves_variant_sources_and_log_then_retires_only_snapshot(self):
        modules, canonical, oldcache = self.fixture()
        allowed = self.root / "runs"
        build = allowed / "owned"
        snapshot(modules, ["SCT.B", "SCT.A"], [], canonical, oldcache, build / "src")
        (build / "receipt.json").write_text(json.dumps({"status": "passed", "compiler_sha256": "compiler"}))
        (build / "source-variant.txt").write_bytes(b"uncommitted variant")
        (build / "failed.log").write_bytes(b"failed attempt")
        result = archive_run(build, allowed, self.root / "archives", self.root / "shared", canonical)
        self.assertFalse(build.exists())
        self.assertTrue(canonical.exists())
        with zipfile.ZipFile(result["archive"]) as z:
            self.assertEqual(z.read("source-variant.txt"), b"uncommitted variant")
            self.assertEqual(z.read("failed.log"), b"failed attempt")
            self.assertFalse(any(n.endswith(".agdai") for n in z.namelist()))
        self.assertEqual(len(seed_interfaces(self.root / "shared", "compiler")), 2)
        self.assertEqual(seed_interfaces(self.root / "shared", "different"), {})

    def test_archive_rejects_wrong_root_or_active_snapshot(self):
        _, canonical, _ = self.fixture()
        with self.assertRaisesRegex(ValueError, "outside"):
            archive_run(canonical, self.root / "runs", self.root / "archives", self.root / "shared")
        build = self.root / "runs/owned"
        build.mkdir(parents=True)
        (build / "RUNNING").write_text("trial")
        with self.assertRaisesRegex(ValueError, "active"):
            archive_run(build, self.root / "runs", self.root / "archives", self.root / "shared")
        self.assertTrue(build.exists())

    def archive_fixture(self):
        modules, canonical, oldcache = self.fixture()
        allowed = self.root / "_build/agda-profile"
        build = allowed / "owned"
        snapshot(modules, ["SCT.B", "SCT.A"], [], canonical, oldcache, build / "src")
        (build / "receipt.json").write_text(json.dumps({
            "status": "passed", "compiler_sha256": "compiler"}), encoding="utf-8")
        return build, allowed, self.root / "archives", self.root / "shared", canonical

    def test_archive_holds_resume_lock_until_retirement(self):
        args = self.archive_fixture()
        build = args[0]
        original_remove = profile_agda.shutil.rmtree
        observed = []

        def guarded_remove(path, *positional, **keywords):
            if Path(path) == build:
                self.assertTrue((build / "RUNNING").is_file())
                self.assertTrue(profile_agda.snapshot_lock_path(build).is_file())
                # Simulate rmtree deleting its internal marker first. The external
                # lock must still block both a stale-reader acquisition and CLI resume.
                (build / "RUNNING").unlink()
                with self.assertRaisesRegex(ValueError, "active"):
                    profile_agda.acquire_snapshot_lock(build, "resume")
                argv = ["profile_agda", "--resume", str(build), "--module", "SCT.A"]
                with patch.object(profile_agda, "ROOT", self.root), \
                     patch.object(sys, "argv", argv), \
                     patch.object(profile_agda.shutil, "which") as find_compiler:
                    with self.assertRaises(SystemExit):
                        profile_agda.main()
                    find_compiler.assert_not_called()
                observed.append(True)
            return original_remove(path, *positional, **keywords)

        with patch.object(profile_agda.shutil, "rmtree", side_effect=guarded_remove):
            result = archive_run(*args)
        self.assertEqual(observed, [True])
        self.assertFalse(profile_agda.snapshot_lock_path(build).exists())
        with zipfile.ZipFile(result["archive"]) as bundle:
            self.assertNotIn("RUNNING", bundle.namelist())

    def test_archive_preflights_compiler_before_creating_zip(self):
        args = self.archive_fixture()
        build, _, archives, cache, _ = args
        cache.mkdir()
        (cache / "manifest.json").write_text(json.dumps({
            "compiler_sha256": "other compiler", "modules": {}}), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "Cache compiler differs"):
            archive_run(*args)
        self.assertTrue(build.exists())
        self.assertFalse((build / "RUNNING").exists())
        self.assertFalse(profile_agda.snapshot_lock_path(build).exists())
        self.assertFalse((archives / "owned.zip").exists())
        self.assertEqual(json.loads((cache / "manifest.json").read_text())["compiler_sha256"],
                         "other compiler")

    def test_archive_retries_verified_zip_after_cache_failure(self):
        args = self.archive_fixture()
        build, _, archives, _, _ = args
        with patch.object(profile_agda, "write_receipt", side_effect=OSError("cache failure")):
            with self.assertRaisesRegex(OSError, "cache failure"):
                archive_run(*args)
        archive = archives / "owned.zip"
        digest = sha256(archive)
        self.assertTrue(build.exists())
        self.assertFalse((build / "RUNNING").exists())
        self.assertFalse(profile_agda.snapshot_lock_path(build).exists())
        result = archive_run(*args)
        self.assertEqual(result["sha256"], digest)
        self.assertFalse(build.exists())

    def test_archive_failed_zip_write_leaves_no_final_archive(self):
        args = self.archive_fixture()
        build, _, archives, _, _ = args
        with patch.object(profile_agda.zipfile.ZipFile, "write", side_effect=OSError("zip failure")):
            with self.assertRaisesRegex(OSError, "zip failure"):
                archive_run(*args)
        self.assertTrue(build.exists())
        self.assertFalse((build / "RUNNING").exists())
        self.assertFalse(profile_agda.snapshot_lock_path(build).exists())
        self.assertFalse((archives / "owned.zip").exists())
        self.assertEqual(list(archives.iterdir()), [])
        archive_run(*args)
        self.assertFalse(build.exists())

    def test_archive_differing_retry_retains_both_versions(self):
        args = self.archive_fixture()
        build, _, archives, _, _ = args
        with patch.object(profile_agda, "write_receipt", side_effect=OSError("cache failure")):
            with self.assertRaises(OSError):
                archive_run(*args)
        archive = archives / "owned.zip"
        digest = sha256(archive)
        (build / "new-note.txt").write_text("Keep this unarchived change.", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "differs from snapshot"):
            archive_run(*args)
        self.assertEqual(sha256(archive), digest)
        self.assertEqual((build / "new-note.txt").read_text(), "Keep this unarchived change.")
        self.assertFalse((build / "RUNNING").exists())
        self.assertFalse(profile_agda.snapshot_lock_path(build).exists())

    def test_archive_rejects_corrupt_existing_archive_without_replacing_it(self):
        args = self.archive_fixture()
        build, _, archives, _, _ = args
        archives.mkdir()
        archive = archives / "owned.zip"
        archive.write_bytes(b"partial old zip")
        with self.assertRaisesRegex(ValueError, "Archive is invalid"):
            archive_run(*args)
        self.assertEqual(archive.read_bytes(), b"partial old zip")
        self.assertTrue(build.exists())
        self.assertFalse((build / "RUNNING").exists())
        self.assertFalse(profile_agda.snapshot_lock_path(build).exists())

    def test_cli_resume_records_variants_without_new_snapshot_or_compiler(self):
        modules, source, _ = self.fixture()
        argv = ["profile_agda", "--module", "SCT.A", "--agda", "fake", "--label", "before"]
        fake = {"status": 0, "seconds": 0, "checked_modules": ["SCT.A"]}
        with patch.object(profile_agda, "ROOT", self.root), patch.object(profile_agda, "SOURCE", source), \
             patch.object(profile_agda, "sources", return_value=modules), \
             patch.object(profile_agda.shutil, "which", return_value=sys.executable), \
             patch.object(profile_agda.subprocess, "check_output", return_value="2.8.0"), \
             patch.object(profile_agda, "run_command", return_value=fake), patch.object(sys, "argv", argv):
            self.assertEqual(profile_agda.main(), 0)
            build = next((self.root / "_build/agda-profile").iterdir())
            first = json.loads((build / "receipt.json").read_text())
            self.assertFalse((build / "RUNNING").exists())
            self.assertFalse(profile_agda.snapshot_lock_path(build).exists())
            copied = build / "src/SCT/A.lagda.md"
            copied.write_bytes(copied.read_bytes() + b"\nNew experimental prose.\n")
            argv[-1] = "after"
            argv.extend(["--resume", str(build)])
            self.assertEqual(profile_agda.main(), 0)
            last = json.loads((build / "receipt.json").read_text())
            self.assertNotEqual(first["manifest"]["SCT.A"]["sha256"], last["manifest"]["SCT.A"]["sha256"])
            self.assertEqual(first["baseline_manifest"], last["baseline_manifest"])
            self.assertTrue((build / "trials/before/receipt.json").exists())
            self.assertEqual((build / "trials/after/changed-sources/SCT/A.lagda.md").read_bytes(), copied.read_bytes())
            with self.assertRaises(SystemExit):
                profile_agda.main()  # A trial cannot silently overwrite its predecessor.
            self.assertEqual(len(list((self.root / "_build/agda-profile").iterdir())), 1)

    def test_timeout_stops_owned_child_and_keeps_output(self):
        code = "import time; print('Checking SCT.Waiting', flush=True); time.sleep(30)"
        log = self.root / "timeout.log"
        row = run_command([sys.executable, "-c", code], log, 0.5, self.root)
        self.assertEqual(row["status"], "timeout")
        self.assertLess(row["seconds"], 5)
        self.assertIn("Checking SCT.Waiting", log.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
