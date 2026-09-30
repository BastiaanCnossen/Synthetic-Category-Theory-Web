"""Profile a small selection of Agda modules without clearing canonical caches.

Each run copies the selected dependency closure and available interfaces into
_build/agda-profile. Only requested modules start without interfaces. Agda checks
the copied interfaces normally, so stale dependencies appear in the receipt.
The receipt describes the snapshot, not a publication build or a whole-tree check.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from check_agda import EXPENSIVE_MODULES, ROOT, SOURCE, sources


def scope(modules, roots):
    """Return a dependency order and put selected dependencies before consumers."""
    if not roots or len(set(roots)) > 8:
        raise ValueError("Select between one and eight entry modules.")
    if any(n.endswith(".Everything") or n == "SCT.WebEdition" for n in roots):
        raise ValueError("Select individual modules, not full aggregates.")
    active, visited, ordered = set(), set(), []

    def visit(name):
        if name in active:
            raise ValueError(f"Import cycle at {name}")
        if name in visited:
            return
        if name not in modules:
            raise ValueError(f"Missing module: {name}")
        if name.endswith(".Everything") or name == "SCT.WebEdition":
            raise ValueError(f"The selected closure includes an aggregate: {name}")
        if name in EXPENSIVE_MODULES:
            raise ValueError(f"The selected closure includes a deferred branch: {name}")
        active.add(name)
        for dependency in sorted(modules[name][1]):
            visit(dependency)
        active.remove(name)
        visited.add(name)
        ordered.append(name)

    for name in sorted(set(roots)):
        visit(name)
    return ordered, [n for n in ordered if n in roots]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(modules, ordered, entries, source, cache, destination):
    """Copy sources exactly; never copy an entry's interface or modify a cache."""
    destination.mkdir(parents=True, exist_ok=False)
    manifest = {}
    for name in ordered:
        original, _, expected = modules[name]
        relative = original.relative_to(source)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(original, target)
        if sha256(target) != expected:
            raise ValueError(f"Source changed while taking the snapshot: {name}")
        row = {"path": relative.as_posix(), "sha256": expected,
               "options": re.findall(r"\{-#\s+OPTIONS\s+(.*?)#-\}",
                                     target.read_text(encoding="utf-8"), re.S)}
        interface = cache / Path(*name.split(".")).with_suffix(".agdai")
        if name not in entries and interface.is_file():
            copied = target.with_name(name.rsplit(".", 1)[-1] + ".agdai")
            shutil.copy2(interface, copied)
            row["interface_sha256"] = sha256(copied)
        manifest[name] = row
    return manifest


def run_command(command, log, timeout, cwd):
    """Stop only the child owned by this invocation, retaining partial output."""
    start = time.perf_counter()
    error = None
    try:
        with log.open("wb") as output:
            child = subprocess.Popen(command, cwd=cwd, stdout=output, stderr=subprocess.STDOUT)
            try:
                status = child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
                status = "timeout"
            except KeyboardInterrupt:
                child.kill()
                child.wait()
                status = "interrupted"
    except OSError as exception:
        status, error = "error", str(exception)
    try:
        contents = log.read_text(encoding="utf-8", errors="replace")
    except OSError as exception:
        contents = ""
        status, error = "error", str(exception)
    row = {"status": status, "seconds": time.perf_counter() - start,
           "command": command, "log": str(log),
           "checked_modules": re.findall(r"Checking (SCT\.[\w.]+)", contents)}
    if error is not None:
        row["error"] = error
    for key, description in [("allocated_bytes", "bytes allocated"),
                             ("maximum_residency_bytes", "bytes maximum residency")]:
        match = re.search(r"([\d,]+) " + description, contents)
        row[key] = int(match.group(1).replace(",", "")) if match else None
    return row


def has_hash(path, expected):
    try:
        return sha256(path) == expected
    except OSError:
        return False


def write_receipt(path, report):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", required=True,
                        help="Individual module to freshly check; repeatable, at most eight.")
    parser.add_argument("--agda", default="agda", help="Path to Agda.")
    parser.add_argument("--timeout", type=float, default=120,
                        help="Seconds per entry, greater than zero and at most 120.")
    parser.add_argument("--profile", choices=["definitions", "modules", "internal"],
                        default="definitions", help="Primary Agda profiling mode.")
    parser.add_argument("--conversion", action="store_true",
                        help="Include conversion, constraint, and metavariable counters.")
    parser.add_argument("--plan", action="store_true", help="Show scope without checking or copying files.")
    args = parser.parse_args()
    if not 0 < args.timeout <= 120:
        parser.error("--timeout must be greater than zero and at most 120.")
    try:
        modules = sources()
        ordered, entries = scope(modules, args.module)
    except ValueError as error:
        parser.error(str(error))
    plan = {"entry_modules": entries, "dependency_count": len(ordered),
            "dependency_order": ordered, "timeout_per_entry": args.timeout}
    if args.plan:
        print(json.dumps(plan, indent=2))
        return 0
    executable = shutil.which(args.agda)
    if not executable:
        parser.error("Agda was not found; supply --agda with its executable path.")
    version = subprocess.check_output([executable, "--numeric-version"], text=True).strip()
    release = re.match(r"\d+(?:\.\d+)+", version)
    if not release:
        parser.error(f"Unrecognized Agda version: {version}")
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    build = ROOT / "_build/agda-profile" / run_id
    copied_source = build / "src"
    cache = ROOT / "agda/_build" / release.group() / "agda/src"
    manifest = snapshot(modules, ordered, entries, SOURCE, cache, copied_source)
    report = dict(plan, agda_version=version, started_utc=datetime.now(timezone.utc).isoformat(),
                  manifest=manifest, checks=[], status="running", publication_build=False)
    receipt = build / "receipt.json"
    write_receipt(receipt, report)
    print(f"Profiling {len(entries)} entries; {len(ordered)} modules in the snapshot.", flush=True)
    print(f"Receipt: {receipt}", flush=True)
    for name in entries:
        target = copied_source / manifest[name]["path"]
        command = [executable, "--transliterate", "--safe", "--without-K", "--no-libraries",
                   "--profile=" + args.profile, "-i", str(copied_source), str(target)]
        if args.conversion:
            command += ["--profile=conversion", "--profile=constraints", "--profile=metas"]
        command += ["+RTS", "-s", "-RTS"]
        log = build / (name + ".log")
        row = dict(run_command(command, log, args.timeout, copied_source), module=name)
        report["checks"].append(row)
        write_receipt(receipt, report)
        print(json.dumps(row), flush=True)
        if row["status"] != 0:
            break
    report["canonical_source_drift"] = [n for n in ordered
        if not has_hash(modules[n][0], manifest[n]["sha256"])]
    report["snapshot_source_drift"] = [n for n in ordered
        if not has_hash(copied_source / manifest[n]["path"], manifest[n]["sha256"])]
    success = (len(report["checks"]) == len(entries)
               and all(r["status"] == 0 for r in report["checks"])
               and not report["snapshot_source_drift"])
    report["status"] = "passed" if success else "incomplete"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_receipt(receipt, report)
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
