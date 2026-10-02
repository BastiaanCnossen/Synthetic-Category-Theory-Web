"""The routine scope must exclude the full slow dependency branch."""

from pathlib import Path
import unittest
import tempfile
import subprocess
import json
from unittest.mock import patch

import check_agda

from check_agda import EXPENSIVE_MODULES, plan, sources, grouped_plan, import_only_aggregate, run_groups
from check_agda_layout import has_safe_options

EXPENSIVE = "SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyUncurrying"
SECOND_EXPENSIVE = "SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying"


def graph(dependencies):
    return {name: (Path(name), set(imports), "test-source-hash") for name, imports in dependencies.items()}


class SourceOptionsTests(unittest.TestCase):
    def test_safe_options_allow_local_inference_settings_and_reordering(self):
        for code in [
            '{-# OPTIONS --safe --without-K #-}',
            '{-# OPTIONS --safe --without-K --lossy-unification #-}',
            '{-# OPTIONS --lossy-unification --without-K --safe #-}',
            '{-# OPTIONS --safe\n --without-K #-}',
            '{-# OPTIONS --safe #-}\n{-# OPTIONS --without-K #-}',
        ]:
            with self.subTest(code=code):
                self.assertTrue(has_safe_options(code))

    def test_missing_or_conflicting_required_options_are_rejected(self):
        for code in [
            '', '{-# OPTIONS --safe #-}', '{-# OPTIONS --without-K #-}',
            '{-# OPTIONS --safe --without-K --with-K #-}',
            '{-# OPTIONS --safe --without-K --no-safe #-}',
            '{-# OPTIONS --safe-suffix --without-K #-}',
        ]:
            with self.subTest(code=code):
                self.assertFalse(has_safe_options(code))


class CheckScopeTests(unittest.TestCase):
    def test_every_configured_slow_root_is_excluded_in_routine_mode(self):
        modules = graph({"SCT.Everything": list(EXPENSIVE_MODULES),
                         **{name: [] for name in EXPENSIVE_MODULES}})
        selected, excluded, entries = plan(modules, [], False)
        self.assertFalse(selected)
        self.assertFalse(entries)
        self.assertEqual(set(excluded), EXPENSIVE_MODULES | {"SCT.Everything"})
        full, omitted, full_entries = plan(modules, [], True)
        self.assertEqual(full, set(modules))
        self.assertFalse(omitted)
        self.assertEqual(full_entries, ["SCT.Everything"])

    def test_both_slow_branches_and_their_consumers_are_excluded(self):
        modules = graph({"SCT.Everything": ["first", "second", "independent"],
                         "first": [EXPENSIVE], "second": [SECOND_EXPENSIVE],
                         EXPENSIVE: ["shared"], SECOND_EXPENSIVE: ["shared"],
                         "independent": [], "shared": []})
        selected, excluded, entries = plan(modules, [], False)
        self.assertEqual(selected, {"shared", "independent"})
        self.assertEqual(set(excluded), {"SCT.Everything", "first", "second",
                                         EXPENSIVE, SECOND_EXPENSIVE})
        self.assertEqual(set(entries), selected)

    def test_transitive_consumers_are_excluded_but_dependencies_are_kept(self):
        modules = graph({"SCT.Everything": ["consumer", "independent"],
                         "consumer": [EXPENSIVE], EXPENSIVE: ["shared"],
                         "independent": ["shared"], "shared": []})
        selected, excluded, entries = plan(modules, [], False)
        self.assertEqual(selected, {"shared", "independent"})
        self.assertEqual(set(excluded), {EXPENSIVE, "consumer", "SCT.Everything"})
        self.assertEqual(entries, ["independent"])

    def test_full_check_retains_every_requested_module(self):
        modules = graph({"SCT.Everything": [EXPENSIVE], EXPENSIVE: []})
        selected, excluded, entries = plan(modules, [], True)
        self.assertEqual(selected, set(modules))
        self.assertEqual(excluded, [])
        self.assertEqual(entries, ["SCT.Everything"])

    def test_chapter_selection_does_not_pull_in_other_aggregates(self):
        modules = graph({"SCT.Everything": [EXPENSIVE], EXPENSIVE: [],
                         "SCT.VolumeI.Chapter02.Everything": ["shared"], "shared": []})
        selected, excluded, entries = plan(modules, [2], False)
        self.assertEqual(selected, {"SCT.VolumeI.Chapter02.Everything", "shared"})
        self.assertEqual(excluded, [])

    def test_missing_import_is_an_error(self):
        with self.assertRaisesRegex(ValueError, "Missing module"):
            plan(graph({"SCT.Everything": ["missing"]}), [], False)

    def test_cycle_cannot_silently_disappear_from_selected_entries(self):
        modules = graph({"SCT.Everything": [EXPENSIVE], EXPENSIVE: ["a"],
                         "a": ["b"], "b": ["a"]})
        with self.assertRaisesRegex(ValueError, "Entry closure"):
            plan(modules, [], False)

    def test_real_routine_entry_closure_matches_declared_scope(self):
        modules = sources()
        selected, excluded, entries = plan(modules, [], False)
        reached = set()

        def visit(name):
            if name not in reached:
                reached.add(name)
                for dependency in modules[name][1]:
                    visit(dependency)

        for entry in entries:
            visit(entry)
        self.assertEqual(reached, selected)
        self.assertNotIn(EXPENSIVE, reached)
        self.assertTrue(set(excluded).isdisjoint(reached))


class GroupedCheckTests(unittest.TestCase):
    def test_dependency_order_and_folder_and_size_boundaries(self):
        modules = graph({"SCT.A.Consumer": ["SCT.Z.Dependency"],
                         "SCT.Z.Dependency": [], "SCT.A.Second": ["SCT.A.Consumer"],
                         "SCT.A.Third": ["SCT.A.Second"]})
        groups, static = grouped_plan(modules, set(modules), 2)
        flat = [n for g in groups for n in g["modules"]]
        self.assertEqual(flat, ["SCT.Z.Dependency", "SCT.A.Consumer", "SCT.A.Second", "SCT.A.Third"])
        self.assertEqual([len(g["modules"]) for g in groups], [1, 2, 1])
        self.assertEqual(static, [])
        self.assertEqual(groups, grouped_plan(dict(reversed(list(modules.items()))), set(modules), 2)[0])

    def test_cycle_is_rejected_even_if_reachable_from_a_root(self):
        with self.assertRaisesRegex(ValueError, "Import cycle"):
            grouped_plan(graph({"SCT.A": ["SCT.B"], "SCT.B": ["SCT.A"]}), {"SCT.A", "SCT.B"})

    def test_missing_selected_dependency_and_invalid_size(self):
        with self.assertRaisesRegex(ValueError, "outside selected"):
            grouped_plan(graph({"SCT.A": ["SCT.B"]}), {"SCT.A"})
        with self.assertRaisesRegex(ValueError, "positive"):
            grouped_plan({}, set(), 0)

    def test_only_strict_import_aggregates_can_be_static(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Everything.agda"
            code = "{-# OPTIONS --safe --without-K #-}\nmodule SCT.Everything where\nimport SCT.A\n"
            path.write_text(code, encoding="utf-8")
            self.assertTrue(import_only_aggregate("SCT.Everything", path))
            modules = {"SCT.Everything": (path, {"SCT.A"}, "hash"), **graph({"SCT.A": []})}
            groups, static = grouped_plan(modules, set(modules))
            self.assertEqual(static, ["SCT.Everything"])
            self.assertEqual(groups[0]["modules"], ["SCT.A"])
            groups, static = grouped_plan(modules, set(modules), check_aggregates=True)
            self.assertEqual(static, [])
            self.assertEqual(groups[-1]["modules"][-1], "SCT.Everything")
            for changed in [code + "x = Set\n", code.replace("import SCT.A", "open import SCT.A public"),
                            code.replace("--without-K", "--without-K --allow-unsolved-metas"),
                            code.replace("where\nimport", "whereimport"),
                            code.replace("import SCT.A\n", "import SCT.Aimport SCT.B\n")]:
                path.write_text(changed, encoding="utf-8")
                self.assertFalse(import_only_aggregate("SCT.Everything", path))
                groups, static = grouped_plan(modules, set(modules))
                self.assertEqual(static, [])

    def test_real_routine_and_full_coverage_with_all_dependency_edges_ordered(self):
        modules = sources()
        for full in [False, True]:
            selected, excluded, _ = plan(modules, [], full)
            groups, static = grouped_plan(modules, selected)
            flat = [n for g in groups for n in g["modules"]]
            self.assertEqual(len(flat), len(set(flat)))
            self.assertEqual(set(flat) | set(static), selected)
            self.assertFalse(set(flat) & set(excluded))
            positions = {n: i for i, n in enumerate(flat)}
            for n in flat:
                for dep in modules[n][1] - set(static):
                    self.assertLess(positions[dep], positions[n])
            self.assertTrue(all(len(g["modules"]) <= 20 for g in groups))

    def run_fixture(self, side_effect):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        build = Path(directory.name)
        groups = [{"id": "group-0001", "folder": "SCT", "modules": ["SCT.A"]},
                  {"id": "group-0002", "folder": "SCT", "modules": ["SCT.B"]}]
        report = {"status": "running"}
        with patch("check_agda.subprocess.run", side_effect=side_effect) as run:
            code = run_groups("agda", build, groups, report, timeout=10)
        return code, report, run, build

    def test_sequential_commands_share_source_and_keep_separate_logs(self):
        code, report, run, build = self.run_fixture([subprocess.CompletedProcess([], 0)] * 2)
        self.assertEqual(code, 0)
        self.assertEqual([c["status"] for c in report["checks"]], ["passed", "passed"])
        commands = [call.args[0] for call in run.call_args_list]
        self.assertEqual(commands[0][5], commands[1][5])
        self.assertNotEqual(commands[0][-1], commands[1][-1])
        self.assertEqual(len(list(build.rglob("agda.log"))), 2)
        self.assertEqual(json.loads((build / "receipt.json").read_text())["checks"], report["checks"])

    def test_failure_leaves_remaining_groups_unrun(self):
        code, report, run, _ = self.run_fixture([subprocess.CompletedProcess([], 251)])
        self.assertEqual(code, 251)
        self.assertEqual(run.call_count, 1)
        self.assertEqual([c["status"] for c in report["checks"]], ["failed", "not-run"])

    def test_timeout_is_recorded_without_running_the_next_group(self):
        code, report, run, _ = self.run_fixture(subprocess.TimeoutExpired("agda", 10))
        self.assertEqual(code, 124)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(report["checks"][0]["status"], "timeout")
        self.assertEqual(report["checks"][1]["status"], "not-run")

    def test_source_drift_cannot_produce_a_success_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            old = graph({"SCT.A": []})
            changed = {"SCT.A": (Path("SCT.A"), set(), "changed")}
            with patch.object(check_agda, "ROOT", Path(directory)), \
                 patch.object(check_agda, "sources", side_effect=[old, changed]), \
                 patch.object(check_agda.shutil, "which", return_value="agda"), \
                 patch.object(check_agda, "run_groups", return_value=0), \
                 patch("sys.argv", ["check_agda.py", "--module", "SCT.A"]):
                self.assertEqual(check_agda.main(), 1)
            receipt = next(Path(directory).rglob("receipt.json"))
            self.assertEqual(json.loads(receipt.read_text())["status"], "sources-changed")


if __name__ == "__main__":
    unittest.main()
