"""Regression checks for portable selection and downstream alias protection."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("restrict_module_applications.py")
PROVIDER = (
    "# Example\r\n\r\n```agda\r\n"
    "module SCT.Selected.Provider where\r\n"
    "module Helper = Library argument\r\n"
    "local = Helper.used\r\n```\r\n"
)
SIBLING = (
    "module SCT.Other where\n"
    "module Local = Library argument\n"
    "value = Local.used\n"
)


def run_rewriter(root, prefixes, windows_paths):
    # Emulate Windows relpath output on Linux too, without changing real I/O paths.
    wrapper = (
        "import os, runpy, sys; "
        "original = os.path.relpath; "
        "os.path.relpath = lambda *a, **k: original(*a, **k).replace('/', chr(92)); "
        "sys.argv = sys.argv[1:]; runpy.run_path(sys.argv[0], run_name='__main__')"
    )
    command = [sys.executable]
    if windows_paths:
        command += ["-c", wrapper]
    command += [str(SCRIPT), str(root), *prefixes]
    return subprocess.run(command, capture_output=True, text=True, check=True, timeout=15)


def write(root, relative, contents):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(contents.encode("utf-8"))
    return path


class RestrictModulePathsTests(unittest.TestCase):
    def check_prefix(self, prefix):
        for windows_paths in (False, True):
            with self.subTest(windows_paths=windows_paths), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                provider = write(root, "SCT/Selected/Provider.lagda.md", PROVIDER)
                sibling = write(root, "SCT/Other.agda", SIBLING)
                run_rewriter(root, [prefix], windows_paths)
                self.assertEqual(
                    provider.read_bytes(),
                    PROVIDER.replace("module Helper = Library argument\r\n",
                                     "module Helper = Library argument\r\n  using (used)\r\n").encode(),
                )
                self.assertEqual(sibling.read_bytes(), SIBLING.encode())

    def test_forward_slash_prefix_selects_only_requested_files(self):
        self.check_prefix("SCT/Selected")

    def test_backslash_prefix_selects_only_requested_files(self):
        self.check_prefix(r"SCT\Selected")

    def check_downstream(self, use):
        for windows_paths in (False, True):
            with self.subTest(windows_paths=windows_paths), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                provider = write(root, "SCT/Selected/Provider.lagda.md", PROVIDER)
                sibling = write(root, "SCT/Other.agda", SIBLING)
                write(root, "SCT/Middle.agda",
                      "module SCT.Middle where\nopen import SCT.Selected.Provider public\n")
                write(root, "SCT/Consumer.agda", "module SCT.Consumer where\n" + use)
                result = run_rewriter(root, [], windows_paths)
                self.assertEqual(provider.read_bytes(), PROVIDER.encode())
                self.assertIn('"skipped_downstream": 1', result.stdout)
                self.assertIn(b"using (used)", sibling.read_bytes())

    def test_transitive_qualified_alias_is_preserved(self):
        self.check_downstream("import SCT.Middle as Middle\nvalue = Middle.Helper.other\n")

    def test_transitive_using_list_alias_is_preserved(self):
        self.check_downstream("open import SCT.Middle using (module Helper)\nvalue = Helper.other\n")


if __name__ == "__main__":
    unittest.main()
