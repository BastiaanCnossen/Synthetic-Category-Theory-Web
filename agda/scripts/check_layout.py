"""Check source layout, imports and aggregate coverage without invoking Agda.

Checks that module names match their paths, that every module uses --safe and
--without-K, that imports resolve and are acyclic, that the Everything
aggregates cover their descendants, and that SCT.WebEdition covers the
selected web sections and nothing from later chapters. Interface files in the
source tree are reported. The web edition's passage correspondence is checked
in the Web repository, against its snapshot.
"""

from functools import cache
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src"


def code_text(source):
    if "```agda" not in source:
        return source
    return "\n".join(re.findall(r"```agda\s*\n(.*?)```", source, re.S))


def has_safe_options(code):
    options = {flag for block in re.findall(r"\{-#\s+OPTIONS\s+(.*?)#-\}", code, re.S)
               for flag in block.split()}
    return ({"--safe", "--without-K"} <= options
            and not {"--with-K", "--no-safe"} & options)


def check_source_cache_layout(root):
    interfaces = sorted(root.rglob("*.agdai"))
    if interfaces:
        examples = ", ".join(str(p.relative_to(root)) for p in interfaces[:3])
        raise ValueError(
            f"Found {len(interfaces)} interface files in canonical src: {examples}. "
            "Keep project interfaces in _build/<version>/agda/src; "
            "exclude *.agdai when copying sources back from snapshots. "
            "Inspect existing cache copies before removing source-adjacent files.")


def modules_of(root):
    modules = {}
    for path in root.rglob("*"):
        if path.suffix != ".agda" and not path.name.endswith(".lagda.md"):
            continue
        name = path.relative_to(root).as_posix().removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")
        if name in modules:
            raise ValueError("Duplicate module: " + name)
        source = path.read_text(encoding="utf-8")
        code = code_text(source)
        declared = re.findall(r"^module (SCT\.[\w.]+)(?=\s)", code, re.M)
        if declared != [name]:
            raise ValueError("Module/path mismatch: " + str(path))
        if not has_safe_options(code):
            raise ValueError("Missing safe options: " + name)
        modules[name] = {"path": path, "source": source,
                         "imports": set(re.findall(r"\bimport (SCT\.[\w.]+)", code))}
    return modules


def check(root=SOURCE):
    check_source_cache_layout(root)
    modules = modules_of(root)
    for name, data in modules.items():
        missing = data["imports"] - modules.keys()
        if missing:
            raise ValueError("Unresolved imports in " + name + ": " + str(sorted(missing)))
    visiting, visited = [], set()

    def visit(name):
        if name in visiting:
            raise ValueError("Import cycle: " + " -> ".join(visiting + [name]))
        if name in visited:
            return
        visiting.append(name)
        for target in modules[name]["imports"]:
            visit(target)
        visiting.pop()
        visited.add(name)

    for name in modules:
        visit(name)

    @cache
    def closure(name):
        result = {name}
        for target in modules[name]["imports"]:
            result.update(closure(target))
        return frozenset(result)

    expected = {name for name in modules if ".VolumeI." in name}
    if not expected <= closure("SCT.Everything"):
        raise ValueError("Full aggregate omits modules: " + str(sorted(expected - closure("SCT.Everything"))))
    for name in modules:
        if name.endswith(".Everything") and ".VolumeI." in name:
            prefix = name.rsplit(".", 1)[0] + "."
            descendants = {n for n in modules if n.startswith(prefix) and n != name}
            missing = descendants - closure(name)
            if missing:
                raise ValueError("Aggregate omits supporting modules in " + name + ": " + str(sorted(missing)))
    web = closure("SCT.WebEdition")
    expected_web = {n for n in modules
                    if re.match(r"SCT\.VolumeI\.(?:Chapter01\.Section0[1-8]|Chapter02\.Section0[1-6])\.", n)}
    if not expected_web <= web:
        raise ValueError("Web aggregate omits selected modules")
    if any(re.match(r"SCT\.VolumeI\.Chapter(?!01\.|02\.|03\.)", n) for n in web):
        raise ValueError("Web aggregate unexpectedly imports later chapters/sections")
    report = {"status": "passed", "source_modules": len(modules),
              "imports": sum(len(x["imports"]) for x in modules.values()),
              "web_source_modules": len(web), "agda_invoked": False}
    print(json.dumps(report))
    return report


if __name__ == "__main__":
    check()
