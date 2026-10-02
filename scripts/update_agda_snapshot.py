"""Replace the web edition's Agda snapshot with a committed state of the Agda repository.

Run only with the author's explicit authorization: the snapshot is what the
public web edition displays and what its CI checks. The source is an exact
commit of the private Agda repository, never its working tree, so the snapshot
can always be traced and reproduced. Usage:

    python scripts/update_agda_snapshot.py --commit <sha> [--agda-repo PATH]

The snapshot replaces agda/src entirely (mirroring deletions), the library and
reading files, and the checking tools under agda/scripts. It records the
commit in agda/SNAPSHOT.json and then runs the structural checks. Interface
caches and the web build are not touched; regenerate the site separately.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / "agda"
# Paths in the Agda repository and where they go in the snapshot.
FILES = {
    "src": "src",
    "sct.agda-lib": "sct.agda-lib",
    "module-layout.json": "module-layout.json",
    "ReadingGuide.md": "ReadingGuide.md",
    "README.md": "README.md",
    "scripts/check_agda.py": "scripts/check_agda.py",
    "scripts/agda_lock.py": "scripts/agda_lock.py",
    "scripts/check_layout.py": "scripts/check_layout.py",
    "scripts/audit_lossy.py": "scripts/audit_lossy.py",
}


def agda_repository(explicit):
    candidates = [explicit] if explicit else [
        os.environ.get("SCT_AGDA"), ROOT.parent / "Agda", ROOT.parent / "Synthetic Category Theory Agda"]
    for candidate in candidates:
        if candidate and (Path(candidate) / "sct.agda-lib").is_file():
            return Path(candidate).resolve()
    raise SystemExit("Agda repository not found; pass --agda-repo or set SCT_AGDA.")


def git(repo, *args, binary=False):
    result = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, check=True)
    return result.stdout if binary else result.stdout.decode("utf-8").strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--commit", required=True, help="Commit of the Agda repository to publish.")
    parser.add_argument("--agda-repo", help="Path to the Agda repository (default: sibling Agda folder).")
    args = parser.parse_args()
    repo = agda_repository(args.agda_repo)
    try:
        commit = git(repo, "rev-parse", "--verify", args.commit + "^{commit}")
    except subprocess.CalledProcessError:
        parser.error(f"Not a commit of {repo}: {args.commit}")
    archive = git(repo, "archive", "--format=tar", commit, *FILES, binary=True)
    staged = ROOT / "_build" / "agda-snapshot-staging"
    if staged.exists():
        shutil.rmtree(staged)
    staged.mkdir(parents=True)
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        bundle.extractall(staged, filter="data")
    for source in FILES:
        if not (staged / source).exists():
            parser.error(f"{source} is missing at {commit}")
    # Replace each snapshot path; src is mirrored so that deletions propagate.
    for source, target in FILES.items():
        destination = SNAPSHOT / target
        if destination.is_dir():
            shutil.rmtree(destination)
        elif destination.exists():
            destination.unlink()
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(staged / source), destination)
    shutil.rmtree(staged)
    sources = sorted(p for p in (SNAPSHOT / "src").rglob("*") if p.is_file())
    digest = hashlib.sha256()
    for path in sources:
        digest.update(path.relative_to(SNAPSHOT).as_posix().encode() + b"\0" + path.read_bytes())
    record = {"repository": "Synthetic-Category-Theory-Agda", "commit": commit,
              "commit_date": git(repo, "show", "-s", "--format=%cI", commit),
              "commit_subject": git(repo, "show", "-s", "--format=%s", commit),
              "updated_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
              "files": sorted(FILES.values()), "source_files": len(sources),
              "source_tree_sha256": digest.hexdigest()}
    (SNAPSHOT / "SNAPSHOT.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, indent=2))
    for check in [[sys.executable, str(SNAPSHOT / "scripts/check_layout.py")],
                  [sys.executable, str(ROOT / "scripts/check_agda_layout.py")]]:
        subprocess.run(check, check=True)
    print("Snapshot updated. Agda has not been run; CI checks it after the snapshot is pushed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
