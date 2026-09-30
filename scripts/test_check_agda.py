"""The routine scope must exclude the full slow dependency branch."""

from pathlib import Path
import unittest

from check_agda import EXPENSIVE_MODULES, plan, sources
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


if __name__ == "__main__":
    unittest.main()
