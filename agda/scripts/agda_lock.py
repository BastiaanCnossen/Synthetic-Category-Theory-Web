"""One Agda compiler at a time: a lock shared by check_agda.py and profile_agda.py.

The lock is a JSON file created exclusively. It names its owner (tool, command,
start time, process and the Agda child currently running). A lock is reclaimed
only when it was written on this host and neither its owner process nor its
recorded child is still running; the age of a lock is never a reason to remove
it. Process identity includes the start time, so a reused process number does
not keep an abandoned lock alive or let a live lock be taken over.
"""

from contextlib import contextmanager
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import socket
import sys
import time

# SCT_AGDA_LOCK names one lock shared by several checkouts (for example the
# formalization and the web snapshot); otherwise each checkout has its own.
DEFAULT_PATH = Path(os.environ.get("SCT_AGDA_LOCK")
                    or Path(__file__).resolve().parents[1] / "_build/agda-compiler.lock")


def process_start(pid):
    """Return an opaque start-time token for a running process, or None if it is not running."""
    if pid is None or pid <= 0:
        return None
    if sys.platform == "win32":
        import ctypes
        from ctypes import wintypes
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel.OpenProcess.restype = wintypes.HANDLE
        handle = kernel.OpenProcess(0x1000, False, pid)  # PROCESS_QUERY_LIMITED_INFORMATION
        if not handle:
            # Access denied means the process exists but belongs to someone else.
            return "unknown" if ctypes.get_last_error() == 5 else None
        try:
            code = wintypes.DWORD()
            if not kernel.GetExitCodeProcess(handle, ctypes.byref(code)) or code.value != 259:
                return None  # 259 is STILL_ACTIVE.
            times = [wintypes.FILETIME() for _ in range(4)]
            if not kernel.GetProcessTimes(handle, *[ctypes.byref(t) for t in times]):
                return "unknown"
            return str((times[0].dwHighDateTime << 32) | times[0].dwLowDateTime)
        finally:
            kernel.CloseHandle(handle)
    stat = Path(f"/proc/{pid}/stat")
    if stat.exists():
        try:
            # The command name may contain spaces; fields resume after its ')'.
            return stat.read_text().rsplit(")", 1)[1].split()[19]
        except (OSError, IndexError):
            return None
    try:
        os.kill(pid, 0)  # POSIX only; on Windows signal 0 would be CTRL_C_EVENT.
    except ProcessLookupError:
        return None
    except PermissionError:
        return "unknown"
    return "unknown"


def alive(pid, token):
    """A recorded process is live if a process with that number runs and has not been replaced."""
    current = process_start(pid)
    if current is None:
        return False
    return current == "unknown" or token in (None, "unknown") or current == token


def read(path=None):
    """Return the current owner record, None if unlocked, or {} while it is being written."""
    try:
        text = Path(path or DEFAULT_PATH).read_text(encoding="utf-8")
    except FileNotFoundError:
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return {}


def abandoned(record):
    """Only an owner on this host whose owner and child have both exited is abandoned."""
    if not record or record.get("host") != socket.gethostname():
        return False
    if alive(record.get("pid"), record.get("pid_start")):
        return False
    return not alive(record.get("child_pid"), record.get("child_start"))


def describe(record):
    if not record:
        return "an owner whose record is being written"
    child = f", Agda process {record['child_pid']}" if record.get("child_pid") else ""
    return (f"{record.get('tool')} (process {record.get('pid')}{child}, since "
            f"{record.get('started_utc')}, host {record.get('host')}): {record.get('description')}")


class CompilerLock:
    """Exclusive owner record; use through ``held`` so that release is guaranteed."""

    def __init__(self, tool, description, path=None):
        self.path = Path(path) if path else DEFAULT_PATH
        pid = os.getpid()
        self.record = {"tool": tool, "description": description, "pid": pid,
                       "pid_start": process_start(pid), "host": socket.gethostname(),
                       "started_utc": datetime.now(timezone.utc).isoformat(),
                       "command": sys.argv, "child_pid": None, "child_start": None}
        self.owned = False

    def _write(self, mode):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        flags = os.O_WRONLY | (os.O_CREAT | os.O_EXCL if mode == "create" else os.O_TRUNC)
        descriptor = os.open(self.path, flags)
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(json.dumps(self.record, indent=2) + "\n")

    def try_acquire(self):
        for _ in range(2):
            try:
                self._write("create")
            except FileExistsError:
                record = read(self.path)
                if record and abandoned(record) and self._reclaim(record):
                    continue  # Retry once immediately after removing an abandoned lock.
                return False
            self.owned = True
            return True
        return False

    def _reclaim(self, record):
        """Move an abandoned record aside, and restore it if a live owner raced us."""
        aside = self.path.with_name(f"{self.path.name}.abandoned-{os.getpid()}-{time.time_ns()}")
        try:
            os.replace(self.path, aside)
        except FileNotFoundError:
            return True
        if read(aside) == record:
            print(f"Removed abandoned Agda compiler lock: {describe(record)}", flush=True)
            aside.unlink(missing_ok=True)
            return True
        try:
            os.link(aside, self.path)  # Atomic; fails if yet another owner exists.
        except FileExistsError:
            pass
        aside.unlink(missing_ok=True)
        return False

    def acquire(self, wait=True, poll=10.0, timeout=None):
        """Wait for the lock (reporting its owner) unless ``wait`` is false."""
        start = time.monotonic()
        reported = None
        while not self.try_acquire():
            record = read(self.path)
            if not wait:
                raise RuntimeError("The Agda compiler is in use by " + describe(record))
            if record is not None and record.get("pid") != reported:
                print("Waiting for the Agda compiler lock held by " + describe(record), flush=True)
                reported = record.get("pid") if record else None
            if timeout is not None and time.monotonic() - start > timeout:
                raise TimeoutError("Timed out waiting for the Agda compiler lock held by "
                                   + describe(record))
            time.sleep(poll)

    def set_child(self, pid):
        """Record the running Agda process so an orphaned compiler keeps the lock held."""
        if not self.owned:
            return
        self.record.update(child_pid=pid, child_start=process_start(pid) if pid else None)
        self._write("update")

    def release(self):
        if not self.owned:
            return
        current = read(self.path)
        if current and current.get("pid") == self.record["pid"] \
                and current.get("pid_start") == self.record["pid_start"]:
            self.path.unlink(missing_ok=True)
        self.owned = False


@contextmanager
def held(tool, description, wait=True, path=None, poll=10.0):
    lock = CompilerLock(tool, description, path)
    lock.acquire(wait=wait, poll=poll)
    try:
        yield lock
    finally:
        lock.release()


def main():
    """Show the current owner, if any."""
    record = read()
    if record is None:
        print("unlocked")
        return 0
    state = "abandoned" if abandoned(record) else "held"
    print(f"{state}: {describe(record)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
