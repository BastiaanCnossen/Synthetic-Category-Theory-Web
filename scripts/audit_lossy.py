"""Check every module that uses --lossy-unification once more without it.

Why: lossy unification cannot make Agda accept a false statement, but it can
solve an implicit argument differently from ordinary unification, which by
default only commits to unique solutions (--require-unique-meta-solutions).
This is a regression audit: it establishes only that every flagged module
also type-checks without the flag. It does NOT compare the elaborated terms
of the two runs, so it does not by itself show that a transparent
construction or chosen comparison is the same term in both. That needs a
separate term comparison, or keeping such constructions out of flagged
modules.

The audit works on a copy under _build/lossy-audit/; canonical sources and
caches are not modified. Reports: _build/lossy-audit/report.md and report.json.
"""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
AGDA = ROOT / "agda"
OUT = ROOT / "_build/lossy-audit"
FLAG = re.compile(r"[ \t]*--lossy-unification")


def module_name(path, src):
    name = path.relative_to(src).as_posix()
    return name.removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agda", default="agda", help="Path to the Agda executable.")
    parser.add_argument("--only", action="append", default=[], help="Restrict to these modules; repeatable.")
    args = parser.parse_args()
    executable = shutil.which(args.agda)
    if not executable:
        parser.error("Agda was not found; supply --agda.")

    tree = OUT / "tree"
    if tree.exists():
        shutil.rmtree(tree)
    tree.mkdir(parents=True)
    shutil.copytree(AGDA / "src", tree / "src")
    shutil.copy(AGDA / "sct.agda-lib", tree / "sct.agda-lib")
    if (AGDA / "_build").exists():  # reuse interfaces of unaffected modules
        shutil.copytree(AGDA / "_build", tree / "_build",
                        ignore=shutil.ignore_patterns("agda-profile*", "*.log", "*.json"))

    lossy = []
    for path in sorted((tree / "src").rglob("*")):
        if not (path.name.endswith(".agda") or path.name.endswith(".lagda.md")):
            continue
        text = path.read_text(encoding="utf-8")
        if "--lossy-unification" not in text:
            continue
        name = module_name(path, tree / "src")
        if args.only and name not in args.only:
            continue
        lossy.append(name)
        path.write_text(FLAG.sub("", text), encoding="utf-8")

    results = []
    for name in lossy:
        path = next(p for p in (tree / "src").rglob("*")
                    if p.is_file() and module_name(p, tree / "src") == name)
        start = time.time()
        with (OUT / f"{name}.log").open("w", encoding="utf-8") as log:
            proc = subprocess.run([executable, "--transliterate", "--safe", "--without-K",
                                   "-i", str(tree / "src"), str(path)],
                                  cwd=tree, stdout=log, stderr=subprocess.STDOUT)
        seconds = round(time.time() - start, 1)
        results.append({"module": name, "passed": proc.returncode == 0, "seconds": seconds})
        print(f"{'passed' if proc.returncode == 0 else 'FAILED'}  {seconds:8.1f}s  {name}", flush=True)

    report = {"finished_utc": datetime.now(timezone.utc).isoformat(), "modules": results,
              "all_passed": all(r["passed"] for r in results)}
    (OUT / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    lines = ["# Lossy-unification audit", "",
             f"{sum(r['passed'] for r in results)} of {len(results)} modules also check without the flag.", "",
             "| Module | Without lossy unification | Seconds |", "|---|---|---|"]
    lines += [f"| `{r['module']}` | {'passes' if r['passed'] else '**fails**'} | {r['seconds']} |" for r in results]
    lines += ["", "Seconds include rechecking any dependency whose flag was also removed."]
    (OUT / "report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
