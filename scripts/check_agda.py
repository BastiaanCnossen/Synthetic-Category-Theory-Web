"""Check the formalization, with the expensive uncurrying branches opt-in.

Routine checks exclude the named bottlenecks and every module depending on them.
The full aggregates and their mathematical coverage are left unchanged.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "agda/src"
EXPENSIVE_MODULES = {
    "SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyUncurrying",
    "SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying",
    "SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingNaturality",
}


def sources():
    result = {}
    for path in SOURCE.rglob("*"):
        if not (path.name.endswith(".agda") or path.name.endswith(".lagda.md")):
            continue
        name = path.relative_to(SOURCE).as_posix()
        name = name.removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")
        contents = path.read_bytes()
        source = contents.decode("utf-8")
        code = "\n".join(re.findall(r"```agda\s*\n(.*?)```", source, re.S)) if "```agda" in source else source
        if name in result:
            raise ValueError(f"Duplicate module: {name}")
        result[name] = (path, set(re.findall(r"\bimport (SCT\.[\w.]+)", code)),
                        hashlib.sha256(contents).hexdigest())
    return result


def plan(modules, chapters, full):
    roots = ([f"SCT.VolumeI.Chapter{n:02d}.Everything" for n in chapters]
             if chapters else ["SCT.Everything"])
    requested = set()

    def visit(name):
        if name in requested:
            return
        if name not in modules:
            raise ValueError(f"Missing module: {name}")
        requested.add(name)
        for dependency in modules[name][1]:
            visit(dependency)

    for root in roots:
        visit(root)
    excluded = set() if full else requested & EXPENSIVE_MODULES
    while True:
        enlarged = excluded | {n for n in requested if modules[n][1] & excluded}
        if enlarged == excluded:
            break
        excluded = enlarged
    selected = requested - excluded
    # Import the maximal selected modules; their closure is exactly selected.
    imported = set().union(*(modules[n][1] for n in selected)) if selected else set()
    entries = sorted(selected - imported)
    reached = set()

    def cover(name):
        if name in reached:
            return
        reached.add(name)
        for dependency in modules[name][1]:
            cover(dependency)

    for entry in entries:
        cover(entry)
    if reached != selected:
        raise ValueError("Entry closure does not equal the selected scope; check import cycles.")
    return selected, sorted(excluded), entries


def hashes(modules, names):
    return {name: modules[name][2] for name in sorted(names)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="Include every theorem in the selected aggregates.")
    parser.add_argument("--chapter", type=int, action="append", default=[], help="Limit to a chapter and its dependencies; repeatable.")
    parser.add_argument("--plan", action="store_true", help="Show the scope without running Agda.")
    parser.add_argument("--agda", default="agda", help="Path to the Agda executable.")
    args = parser.parse_args()
    try:
        modules = sources()
        selected, excluded, entries = plan(modules, args.chapter, args.full)
    except ValueError as error:
        parser.error(str(error))
    mode = "full" if args.full else "routine"
    scope = "chapters-" + "-".join(map(str, sorted(set(args.chapter)))) if args.chapter else "all"
    report = {"mode": mode, "scope": scope, "selected_modules": len(selected),
              "excluded_modules": excluded, "entry_modules": entries}
    if args.plan:
        print(json.dumps(report, indent=2))
        return 0
    executable = shutil.which(args.agda)
    if not executable:
        parser.error("Agda was not found; supply --agda with its executable path.")
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    build = ROOT / "_build/agda-check" / mode / scope / run_id
    build.mkdir(parents=True, exist_ok=True)
    target = build / "CheckSelected.agda"
    target.write_text("{-# OPTIONS --safe --without-K #-}\nmodule CheckSelected where\n\n" +
                      "".join(f"import {name}\n" for name in entries), encoding="utf-8")
    command = [executable, "--transliterate", "--safe", "--without-K",
               "-i", str(SOURCE), "-i", str(build), str(target)]
    report.update(command=command, started_utc=datetime.now(timezone.utc).isoformat(),
                  before=hashes(modules, selected), status="running")
    receipt = build / "receipt.json"
    receipt.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"Checking {len(selected)} modules ({mode}); {len(excluded)} excluded.", flush=True)
    for name in excluded:
        print(f"Excluded: {name}", flush=True)
    print(f"Log: {build / 'agda.log'}", flush=True)
    with (build / "agda.log").open("w", encoding="utf-8") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report.update(exit_code=result.returncode, finished_utc=datetime.now(timezone.utc).isoformat(),
                  stable_sources=False)
    try:
        after_modules = sources()
        after_selected, after_excluded, _ = plan(after_modules, args.chapter, args.full)
        report["after"] = hashes(after_modules, after_selected)
        report["stable_sources"] = (report["before"] == report["after"] and excluded == after_excluded)
    except (ValueError, OSError) as error:
        report["source_change_error"] = str(error)
    report["status"] = ("passed" if not result.returncode and report["stable_sources"]
                        else "failed" if result.returncode else "sources-changed")
    receipt.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"{report['status']}: {receipt}", flush=True)
    return result.returncode or (0 if report["stable_sources"] else 1)


if __name__ == "__main__":
    raise SystemExit(main())
