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
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import zipfile

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


def snapshot(modules, ordered, entries, source, cache, destination, seed=None):
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
        if seed and name in seed:
            candidate, source_hash, interface_hash = seed[name]
            if expected == source_hash and has_hash(candidate, interface_hash):
                interface = candidate
        if name not in entries and interface.is_file():
            copied = target.with_name(name.rsplit(".", 1)[-1] + ".agdai")
            shutil.copy2(interface, copied)
            row["interface_sha256"] = sha256(copied)
            row["interface_origin"] = str(interface)
        manifest[name] = row
    return manifest


def snapshot_modules(source):
    """Read an editable snapshot, including changed imports, without touching canonical files."""
    result = {}
    source = source.resolve()
    for path in source.rglob("*"):
        if not (path.name.endswith(".agda") or path.name.endswith(".lagda.md")):
            continue
        if not path.resolve().is_relative_to(source):
            raise ValueError(f"Snapshot source escapes its root: {path}")
        name = path.relative_to(source).as_posix()
        name = name.removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")
        text = path.read_text(encoding="utf-8")
        code = "\n".join(re.findall(r"```agda\s*\n(.*?)```", text, re.S)) if "```agda" in text else text
        if name in result:
            raise ValueError(f"Duplicate snapshot module: {name}")
        result[name] = (path, set(re.findall(r"\bimport (SCT\.[\w.]+)", code)), sha256(path))
    return result


def seed_interfaces(cache, compiler_hash):
    """Cache entries are candidates only; Agda still validates their dependencies."""
    manifest = cache / "manifest.json"
    if not manifest.exists():
        return {}
    record = json.loads(manifest.read_text(encoding="utf-8"))
    if record.get("compiler_sha256") != compiler_hash:
        return {}
    result = {}
    for name, row in record["modules"].items():
        path = (cache / row["interface_path"]).resolve()
        if not path.is_relative_to(cache.resolve()):
            raise ValueError("Shared cache path escapes its root")
        result[name] = (path, row["source_sha256"], row["interface_sha256"])
    return result


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



def snapshot_lock_path(build):
    # This marker survives deletion of RUNNING and the entire snapshot tree.
    return build.parent / (".snapshot-" + build.name + ".lock")


def acquire_snapshot_lock(build, owner):
    """Keep exclusion outside the tree; RUNNING remains an interruption marker."""
    external = snapshot_lock_path(build)
    try:
        with external.open("x", encoding="utf-8") as lock:
            lock.write(owner + "\n")
    except FileExistsError as error:
        raise ValueError("The snapshot has an active or interrupted run; inspect its sibling lock") from error
    try:
        with (build / "RUNNING").open("x", encoding="utf-8") as lock:
            lock.write(owner + "\n")
    except BaseException as error:
        external.unlink(missing_ok=True)
        if isinstance(error, FileExistsError):
            raise ValueError("The snapshot has an active or interrupted run; inspect RUNNING") from error
        raise


def release_snapshot_lock(build):
    (build / "RUNNING").unlink(missing_ok=True)
    snapshot_lock_path(build).unlink(missing_ok=True)


def verify_archive(archive, kept):
    """Only reuse an archive whose complete contents match this snapshot."""
    try:
        with zipfile.ZipFile(archive) as bundle:
            names = bundle.namelist()
            if (len(names) != len(kept) + 1
                    or set(names) != set(kept) | {"ARCHIVE-MANIFEST.json"}
                    or json.loads(bundle.read("ARCHIVE-MANIFEST.json")) != kept):
                raise ValueError("Archive differs from snapshot; both retained")
            for relative, digest in kept.items():
                if hashlib.sha256(bundle.read(relative)).hexdigest() != digest:
                    raise ValueError("Archive differs from snapshot; both retained")
    except (zipfile.BadZipFile, KeyError, json.JSONDecodeError, UnicodeDecodeError) as error:
        raise ValueError("Archive is invalid; archive and snapshot retained") from error


def archive_run(build, allowed, archives, cache, canonical=SOURCE):
    """Verify a recoverable archive before removing one completed, owned snapshot."""
    build, allowed = build.resolve(), allowed.resolve()
    if build == allowed or not build.is_relative_to(allowed):
        raise ValueError("Archive target is outside the profiler workspace")
    acquire_snapshot_lock(build, "archive")
    try:
        return archive_locked(build, archives, cache, canonical)
    finally:
        # The sibling lock remains held even after rmtree removes RUNNING.
        # On failure release our markers so the verified archive can be retried.
        release_snapshot_lock(build)


def archive_locked(build, archives, cache, canonical):
    receipt = build / "receipt.json"
    if not receipt.is_file():
        raise ValueError("A completed profiler receipt is required")
    report = json.loads(receipt.read_text(encoding="utf-8"))
    if report.get("status") == "running":
        raise ValueError("The snapshot is still running")
    cache_manifest = cache / "manifest.json"
    seed = json.loads(cache_manifest.read_text(encoding="utf-8")) if cache_manifest.exists() else {
        "compiler_sha256": report["compiler_sha256"], "modules": {}}
    if seed["compiler_sha256"] != report["compiler_sha256"]:
        raise ValueError("Cache compiler differs; snapshot retained, no archive created")
    files = [p for p in build.rglob("*") if p.is_file()]
    if any(not p.resolve().is_relative_to(build) for p in files):
        raise ValueError("A snapshot file escapes its root")
    archives.mkdir(parents=True, exist_ok=True)
    archive = archives / (build.name + ".zip")
    kept = {p.relative_to(build).as_posix(): sha256(p)
            for p in files if p.suffix != ".agdai" and p != build / "RUNNING"}
    if "ARCHIVE-MANIFEST.json" in kept:
        raise ValueError("Snapshot contains the reserved archive manifest path; retained")
    if not archive.exists():
        # Publish only a complete verified ZIP. A failed write leaves no final
        # archive, and an existing archive is never replaced, including races.
        with tempfile.TemporaryDirectory(prefix=build.name + "-", dir=archives) as temporary:
            pending = Path(temporary) / "archive.zip"
            with zipfile.ZipFile(pending, "x", zipfile.ZIP_DEFLATED) as bundle:
                for relative in kept:
                    bundle.write(build / relative, relative)
                bundle.writestr("ARCHIVE-MANIFEST.json", json.dumps(kept, indent=2))
            verify_archive(pending, kept)
            try:
                os.link(pending, archive)
            except FileExistsError:
                pass  # Verify a concurrently supplied archive below; never replace it.
    verify_archive(archive, kept)
    # Keep one current-source interface candidate per module. Agda validates it on reuse.
    cache.mkdir(parents=True, exist_ok=True)
    for name, (source, _, digest) in snapshot_modules(build / "src").items():
        relative = source.relative_to(build / "src")
        interface = source.with_name(name.rsplit(".", 1)[-1] + ".agdai")
        if interface.is_file() and has_hash(canonical / relative, digest):
            dest = cache / Path(*name.split(".")).with_suffix(".agdai")
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(interface, dest)
            seed["modules"][name] = {"source_sha256": digest,
                "interface_sha256": sha256(dest), "interface_path": dest.relative_to(cache).as_posix()}
    write_receipt(cache_manifest, seed)
    # Do not delete sources/logs changed while archiving.
    current = {p.relative_to(build).as_posix(): sha256(p) for p in build.rglob("*")
               if p.is_file() and p.suffix != ".agdai" and p != build / "RUNNING"}
    if current != kept:
        raise ValueError("Snapshot changed during archiving; retained")
    shutil.rmtree(build)
    return {"archive": str(archive), "sha256": sha256(archive),
            "files_preserved": len(kept), "cache_candidates": len(seed["modules"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", default=[],
                        help="Individual module to freshly check; repeatable, at most eight.")
    parser.add_argument("--agda", default="agda", help="Path to Agda.")
    parser.add_argument("--timeout", type=float, default=120,
                        help="Seconds per entry, greater than zero and at most 120.")
    parser.add_argument("--profile", choices=["definitions", "modules", "internal"],
                        default="definitions", help="Primary Agda profiling mode.")
    parser.add_argument("--conversion", action="store_true",
                        help="Include conversion, constraint, and metavariable counters.")
    parser.add_argument("--plan", action="store_true", help="Show scope without checking or copying files.")
    parser.add_argument("--resume", type=Path,
                        help="Reuse an editable snapshot under _build/agda-profile.")
    parser.add_argument("--label", default="baseline",
                        help="Unique trial label within the snapshot; existing trials are never overwritten.")
    parser.add_argument("--archive", action="store_true",
                        help="Archive --resume snapshot and retain reusable cache candidates; no compiler run.")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-zA-Z][a-zA-Z0-9_-]{0,63}", args.label):
        parser.error("Use a short alphanumeric trial label starting with a letter.")
    build = None
    previous = None
    if args.resume:
        build = args.resume.resolve()
        allowed = (ROOT / "_build/agda-profile").resolve()
        if not build.is_relative_to(allowed) or build == allowed or not (build / "receipt.json").is_file():
            parser.error("--resume must name an existing bounded-profiler snapshot.")
        previous = json.loads((build / "receipt.json").read_text(encoding="utf-8"))
        if not args.archive and (build / "trials" / args.label).exists():
            parser.error("This trial label already exists; choose another label.")
    if args.archive:
        if not build or args.module or args.plan:
            parser.error("--archive requires --resume and no --module or --plan.")
        try:
            print(json.dumps(archive_run(build, ROOT / "_build/agda-profile",
                ROOT / "agda/bench/archive", ROOT / "_build/agda-profile/cache")))
        except ValueError as error:
            parser.error(str(error))
        return 0
    if build and ((build / "RUNNING").exists() or snapshot_lock_path(build).exists()):
        parser.error("Snapshot has an active or interrupted run; inspect RUNNING and its sibling lock before resuming.")
    if not 0 < args.timeout <= 120:
        parser.error("--timeout must be greater than zero and at most 120.")
    try:
        modules = snapshot_modules(build / "src") if build else sources()
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
    compiler_hash = sha256(Path(executable))
    if previous and previous.get("compiler_sha256") != compiler_hash:
        parser.error("The resumed trial must use the same compiler binary.")
    if build is None:
        run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        build = ROOT / "_build/agda-profile" / run_id
        copied_source = build / "src"
        cache = ROOT / "agda/_build" / release.group() / "agda/src"
        seed = seed_interfaces(ROOT / "_build/agda-profile/cache", compiler_hash)
        manifest = snapshot(modules, ordered, entries, SOURCE, cache, copied_source, seed)
        baseline_manifest = manifest
        with zipfile.ZipFile(build / "baseline-sources.zip", "x", zipfile.ZIP_DEFLATED) as archive:
            for row in manifest.values():
                archive.write(copied_source / row["path"], row["path"])
    else:
        copied_source = build / "src"
        manifest = {n: {"path": modules[n][0].relative_to(copied_source).as_posix(),
                        "sha256": modules[n][2]} for n in ordered}
        baseline_manifest = previous["baseline_manifest"]
    try:
        acquire_snapshot_lock(build, args.label)
    except ValueError as error:
        parser.error(str(error))
    trial = build / "trials" / args.label
    trial.mkdir(parents=True, exist_ok=False)
    for name, row in manifest.items():
        if baseline_manifest.get(name, {}).get("sha256") != row["sha256"]:
            saved = trial / "changed-sources" / row["path"]
            saved.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(copied_source / row["path"], saved)
    report = dict(plan, agda_version=version, started_utc=datetime.now(timezone.utc).isoformat(),
                  manifest=manifest, baseline_manifest=baseline_manifest,
                  compiler_sha256=compiler_hash, trial=args.label,
                  checks=[], status="running", publication_build=False)
    receipt = trial / "receipt.json"
    write_receipt(receipt, report)
    print(f"Profiling {len(entries)} entries; {len(ordered)} modules in the snapshot.", flush=True)
    print(f"Receipt: {receipt}", flush=True)
    for name in entries:
        target = copied_source / manifest[name]["path"]
        interface = target.with_name(name.rsplit(".", 1)[-1] + ".agdai")
        if interface.exists():
            interface.unlink()
        command = [executable, "--transliterate", "--safe", "--without-K", "--no-libraries",
                   "--profile=" + args.profile, "-i", str(copied_source), str(target)]
        if args.conversion:
            command += ["--profile=conversion", "--profile=constraints", "--profile=metas"]
        command += ["+RTS", "-s", "-RTS"]
        log = trial / (name + ".log")
        row = dict(run_command(command, log, args.timeout, copied_source), module=name,
                   source_sha256=manifest[name]["sha256"])
        row["interface_bytes"] = interface.stat().st_size if interface.exists() else None
        report["checks"].append(row)
        write_receipt(receipt, report)
        print(json.dumps(row), flush=True)
        if row["status"] != 0:
            break
    report["canonical_source_drift"] = [n for n in ordered
        if not has_hash(SOURCE / manifest[n]["path"], manifest[n]["sha256"])]
    report["snapshot_source_drift"] = [n for n in ordered
        if not has_hash(copied_source / manifest[n]["path"], manifest[n]["sha256"])]
    success = (len(report["checks"]) == len(entries)
               and all(r["status"] == 0 for r in report["checks"])
               and not report["snapshot_source_drift"])
    report["status"] = "passed" if success else "incomplete"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_receipt(receipt, report)
    write_receipt(build / "receipt.json", report)
    release_snapshot_lock(build)
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
