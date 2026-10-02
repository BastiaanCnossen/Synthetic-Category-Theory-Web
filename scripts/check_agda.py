"""Check the formalization, with the expensive uncurrying branches opt-in.

Routine checks exclude the named bottlenecks and every module depending on them.
Sequential, dependency-ordered groups share the canonical interface cache.
Import-only Everything modules are audited statically unless --check-aggregates
is requested. --full includes the slow branches; it is not a publication build.
"""

import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

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


def plan(modules, chapters, full, roots=None):
    roots = roots or ([f"SCT.VolumeI.Chapter{n:02d}.Everything" for n in chapters]
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


def import_only_aggregate(name, path):
    """Recognize only the exact, declaration-free aggregate grammar we can audit."""
    if not name.endswith(".Everything") or path.suffix != ".agda":
        return False
    code = path.read_text(encoding="utf-8-sig")
    # Only whole-line comments are accepted here. Anything more elaborate is
    # conservatively sent to Agda, including extra options and public imports.
    code = re.sub(r"(?m)^\s*--[^\n]*", "", code)
    pattern = (r"\s*\{-# OPTIONS --safe --without-K #-\}\s*module "
               + re.escape(name) + r" where"
               + r"(?:\s+import SCT\.[\w.]+)*\s*")
    return re.fullmatch(pattern, code) is not None


def group_area(name):
    match = re.match(r"SCT\.VolumeI\.Chapter\d+\.(?:Section\d+|RelativeCategories)(?=\.)", name)
    return match.group(0) if match else name.rsplit(".", 1)[0]


def grouped_plan(modules, selected, batch_size=20, check_aggregates=False):
    """Partition in dependency order; preserve all nontrivial source modules."""
    if batch_size < 1:
        raise ValueError("Batch size must be positive.")
    active, visited = set(), set()

    def visit(name):
        if name in active:
            raise ValueError("Import cycle at " + name)
        if name in visited:
            return
        if name not in selected:
            raise ValueError("Dependency outside selected scope: " + name)
        active.add(name)
        for dependency in sorted(modules[name][1]):
            visit(dependency)
        active.remove(name)
        visited.add(name)

    for name in sorted(selected):
        visit(name)
    static = {name for name in selected
              if not check_aggregates and import_only_aggregate(name, modules[name][0])}
    # Schedule ready modules from the same folder together. A DFS alone keeps
    # returning to a folder after visiting each dependency and creates hundreds
    # of avoidable tiny processes. Dependencies still always precede consumers.
    pending = {name: set(modules[name][1]) for name in selected}
    consumers = {name: set() for name in selected}
    for name, dependencies in pending.items():
        for dependency in dependencies:
            consumers[dependency].add(name)
    ready = {name for name, dependencies in pending.items() if not dependencies}
    order = []
    current_folder = current_area = None
    while ready:
        name = min(ready, key=lambda n: (
            group_area(n) != current_area, n.rsplit(".", 1)[0] != current_folder, n))
        ready.remove(name)
        order.append(name)
        if name not in static:
            current_folder = name.rsplit(".", 1)[0]
            current_area = group_area(name)
        for consumer in consumers[name]:
            pending[consumer].remove(name)
            if not pending[consumer]:
                ready.add(consumer)
    groups = []
    for name in order:
        if name in static:
            continue
        folder = group_area(name)
        if not groups or groups[-1]["folder"] != folder or len(groups[-1]["modules"]) >= batch_size:
            groups.append({"id": f"group-{len(groups) + 1:04d}", "folder": folder,
                           "modules": []})
        groups[-1]["modules"].append(name)
    compiled = {name for group in groups for name in group["modules"]}
    if compiled | static != selected or compiled & static:
        raise ValueError("Grouped coverage differs from the selected scope.")
    return groups, sorted(static)


def run_groups(executable, build, groups, report, timeout=0):
    """One child at a time, same canonical source tree and Agda interface cache."""
    checks = [dict(group, status="not-run") for group in groups]
    report["checks"] = checks
    receipt = build / "receipt.json"

    def save():
        receipt.write_text(json.dumps(report, indent=2), encoding="utf-8")

    save()
    for index, check in enumerate(checks, 1):
        directory = build / check["id"]
        directory.mkdir()
        target = directory / "CheckGroup.agda"
        target.write_text("{-# OPTIONS --safe --without-K #-}\nmodule CheckGroup where\n\n" +
                          "".join(f"import {name}\n" for name in check["modules"]), encoding="utf-8")
        command = [executable, "--transliterate", "--safe", "--without-K",
                   "-i", str(SOURCE), "-i", str(directory), str(target)]
        log_path = directory / "agda.log"
        check.update(command=command, log=str(log_path), status="running",
                     started_utc=datetime.now(timezone.utc).isoformat())
        save()
        print(f"[{index}/{len(checks)}] {check['id']} {check['folder']} "
              f"({len(check['modules'])} modules)\nLog: {log_path}", flush=True)
        started = time.monotonic()
        try:
            with log_path.open("w", encoding="utf-8") as log:
                result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                        timeout=timeout or None)
            code = result.returncode
            check.update(exit_code=code, status="passed" if code == 0 else "failed")
        except subprocess.TimeoutExpired:
            code = 124
            check.update(exit_code=code, status="timeout")
        except OSError as error:
            code = 1
            check.update(exit_code=code, status="failed", error=str(error))
        except KeyboardInterrupt:
            code = 130
            check.update(exit_code=code, status="interrupted")
        check.update(seconds=round(time.monotonic() - started, 3),
                     finished_utc=datetime.now(timezone.utc).isoformat())
        save()
        print(f"{check['id']}: {check['status']} ({check['seconds']} s)", flush=True)
        if code:
            # Print useful diagnostics in Actions as well as retaining the full log.
            if log_path.exists():
                with log_path.open(encoding="utf-8", errors="replace") as log:
                    print("".join(deque(log, maxlen=30)), flush=True)
            return code
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="Include the slow branches in the selected source coverage.")
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--chapter", type=int, action="append", default=[], help="A chapter and its dependencies; repeatable.")
    selection.add_argument("--module", action="append", default=[], help="An explicit module and its dependencies; repeatable.")
    parser.add_argument("--batch-size", type=int, default=20, help="Maximum explicit modules per process (default 20); dependencies may be larger.")
    parser.add_argument("--check-aggregates", action="store_true", help="Also compile import-only Everything modules; may require substantial memory.")
    parser.add_argument("--timeout", type=int, default=0, help="Seconds per group; 0 means no local timeout.")
    parser.add_argument("--plan", action="store_true", help="Show groups and coverage without running Agda.")
    parser.add_argument("--agda", default="agda", help="Path to the Agda executable.")
    args = parser.parse_args()
    if args.timeout < 0:
        parser.error("Timeout must be nonnegative.")
    try:
        modules = sources()
        selected, excluded, entries = plan(modules, args.chapter, args.full, args.module)
        groups, static = grouped_plan(modules, selected, args.batch_size, args.check_aggregates)
    except ValueError as error:
        parser.error(str(error))
    mode = "full" if args.full else "routine"
    scope = ("modules" if args.module else
             "chapters-" + "-".join(map(str, sorted(set(args.chapter)))) if args.chapter else "all")
    report = {"mode": mode, "scope": scope, "selected_modules": len(selected),
              "excluded_modules": excluded, "entry_modules": entries,
              "groups": groups, "batch_size": args.batch_size,
              "static_import_aggregates": static, "publication_build": False,
              "aggregate_check": "compiler" if args.check_aggregates else "static-import-coverage",
              "timeout_per_group": args.timeout}
    if args.plan:
        print(json.dumps(report, indent=2))
        return 0
    executable = shutil.which(args.agda)
    if not executable:
        parser.error("Agda was not found; supply --agda with its executable path.")
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    build = ROOT / "_build/agda-check" / mode / scope / run_id
    build.mkdir(parents=True, exist_ok=True)
    report.update(started_utc=datetime.now(timezone.utc).isoformat(),
                  before=hashes(modules, selected), status="running")
    print(f"Checking {len(selected) - len(static)} source modules in {len(groups)} sequential groups "
          f"({mode}); {len(static)} import-only aggregates audited statically; {len(excluded)} excluded.", flush=True)
    for name in excluded:
        print(f"Excluded: {name}", flush=True)
    code = run_groups(executable, build, groups, report, args.timeout)
    report.update(exit_code=code, finished_utc=datetime.now(timezone.utc).isoformat(), stable_sources=False)
    try:
        after_modules = sources()
        after_selected, after_excluded, _ = plan(after_modules, args.chapter, args.full, args.module)
        report["after"] = hashes(after_modules, after_selected)
        report["stable_sources"] = (report["before"] == report["after"] and excluded == after_excluded)
    except (ValueError, OSError) as error:
        report["source_change_error"] = str(error)
    report["status"] = ("passed" if not code and report["stable_sources"]
                        else "failed" if code else "sources-changed")
    receipt = build / "receipt.json"
    receipt.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"{report['status']}: {receipt}", flush=True)
    return code or (0 if report["stable_sources"] else 1)


if __name__ == "__main__":
    raise SystemExit(main())
