"""Tests for restrict_module_applications_resolved.py (static; no Agda needed)."""
from pathlib import Path
import subprocess, sys, tempfile, unittest, json
SCRIPT = Path(__file__).with_name("restrict_module_applications_resolved.py")
PROVIDER = ("# Example\r\n\r\n```agda\r\nmodule SCT.Selected.Provider where\r\n"
            "module Helper = Library argument\r\nlocal = Helper.used\r\n```\r\n")
LIB = "module SCT.Library (x : X) where\nused : T\nother : T\n_∙_ : T\nmodule Sub where\n  s : T\n"

def run(root, *extra):
    return subprocess.run([sys.executable, str(SCRIPT), str(root), *extra], capture_output=True, text=True, check=True, timeout=30)

def write(root, rel, s):
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(s.encode()); return p

class T(unittest.TestCase):
    def go(self, consumer, provider=PROVIDER):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prov = write(root, "SCT/Selected/Provider.lagda.md", provider)
            write(root, "SCT/Library.agda", LIB)
            write(root, "SCT/Middle.agda", "module SCT.Middle where\nopen import SCT.Selected.Provider public\n")
            write(root, "SCT/Consumer.agda", "module SCT.Consumer where\n" + consumer)
            out = run(root)
            return prov.read_bytes().decode(), out.stdout

    def test_local_only(self):
        s, _ = self.go("")
        self.assertIn("module Helper = Library argument\r\n  using (used)\r\n", s)

    def test_transitive_qualified_alias(self):
        s, _ = self.go("import SCT.Middle as Middle\nvalue = Middle.Helper.other\n")
        self.assertIn("using (other; used)\r\n", s)

    def test_transitive_using_module(self):
        s, _ = self.go("open import SCT.Middle using (module Helper)\nvalue = Helper.other\n")
        self.assertIn("using (other; used)\r\n", s)

    def test_alias_of_alias(self):
        s, _ = self.go("open import SCT.Middle\nmodule H = Helper\nvalue = H.other\n")
        self.assertIn("using (other; used)\r\n", s)

    def test_alias_to_submodule(self):
        s, _ = self.go("open import SCT.Middle\nmodule S = Helper.Sub\nvalue = S.s\n")
        self.assertIn("using (used; module Sub)\r\n", s)

    def test_open_using(self):
        s, _ = self.go("open import SCT.Middle\nopen Helper using (other)\n")
        self.assertIn("using (other; used)\r\n", s)

    def test_wholesale_open_is_skipped(self):
        s, out = self.go("open import SCT.Middle\nopen Helper\nvalue = other\n")
        self.assertNotIn("using", s)
        self.assertIn('"skipped_unresolvable": 1', out)

    def test_hidden_by_using_list(self):
        s, _ = self.go("open import SCT.Middle using ()\nmodule Helper = Foo\nvalue = Helper.zzz\n")
        self.assertIn("using (used)\r\n", s)

    def test_private_is_local_only(self):
        prov = PROVIDER.replace("module Helper = Library argument\r\n", "private\r\n  module Helper = Library argument\r\n")
        s, _ = self.go("import SCT.Middle as Middle\nvalue = Middle.Helper.other\n", prov)
        self.assertIn("  module Helper = Library argument\r\n    using (used)\r\n", s)

    def test_sibling_local_names_not_mixed(self):
        prov = ("```agda\r\nmodule SCT.Selected.Provider where\r\nmodule A where\r\n  module W = Library a\r\n  x = W.used\r\n"
                "module B where\r\n  module W = Library b\r\n  y = W.other\r\n```\r\n")
        s, _ = self.go("", prov)
        self.assertIn("module W = Library a\r\n    using (used)\r\n", s)
        self.assertIn("module W = Library b\r\n    using (other)\r\n", s)

    def test_where_block_used_above(self):
        prov = ("```agda\r\nmodule SCT.Selected.Provider where\r\nfoo : T\r\nfoo = bar\r\n  (W.used)\r\n  where\r\n  module W = Library a\r\n"
                "baz : T\r\nbaz = W.other\r\n  where\r\n    module W = Library b\r\n```\r\n")
        s, _ = self.go("", prov)
        self.assertIn("module W = Library a\r\n    using (used)\r\n", s)
        self.assertIn("module W = Library b\r\n      using (other)\r\n", s)

    def test_scope_continues_in_next_code_block(self):
        prov = ("```agda\r\nmodule SCT.Selected.Provider where\r\nmodule A where\r\n  module W = Library a\r\n  x = W.used\r\n```\r\n"
                "Some prose.\r\n\r\n```agda\r\n  y = W.other\r\n```\r\n")
        s, _ = self.go("", prov)
        self.assertIn("module W = Library a\r\n    using (other; used)\r\n", s)

    def test_instantiation_of_enclosing_module(self):
        prov = ("```agda\r\nmodule SCT.Selected.Provider where\r\nmodule P (z : Z) where\r\n  module W = Library z\r\n  x = W.used\r\n```\r\n")
        s, _ = self.go("open import SCT.Selected.Provider using (module P)\nmodule L = P zero\nvalue = L.W.other\n", prov)
        self.assertIn("module W = Library z\r\n    using (other; used)\r\n", s)

    def test_dry_run_changes_nothing(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); p = write(root, "SCT/Selected/Provider.lagda.md", PROVIDER); write(root, "SCT/Library.agda", LIB)
            run(root, "--dry-run"); self.assertEqual(p.read_bytes().decode(), PROVIDER)

if __name__ == "__main__":
    unittest.main()
