"""
Global one-at-a-time lock for `lean` invocations (mkdir-based, so lean_check.sh can
share it).  A Mathlib-importing `lean` process takes 2–4 GB; this machine has 16 GB and
several agents may run concurrently, so every script that spawns `lean` must hold this.

    from leanlock import lean_lock
    with lean_lock():
        subprocess.run(["lean", ...])

Lock dir: cleanup/.lean.lock/ containing `pid`.  A lock whose pid is dead is stale and
is reclaimed.  Wait time is unbounded (prints a note every 60 s).
"""

from __future__ import annotations

import contextlib
import os
import time
from pathlib import Path

LOCK = Path(__file__).resolve().parent.parent / "cleanup" / ".lean.lock"


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


@contextlib.contextmanager
def lean_lock():
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    waited = 0
    while True:
        try:
            LOCK.mkdir()
            (LOCK / "pid").write_text(str(os.getpid()))
            break
        except FileExistsError:
            try:
                pid = int((LOCK / "pid").read_text().strip() or "0")
            except (FileNotFoundError, ValueError):
                pid = 0
            if pid and not _pid_alive(pid):
                # stale lock from a crashed process
                with contextlib.suppress(FileNotFoundError):
                    (LOCK / "pid").unlink()
                with contextlib.suppress(OSError):
                    LOCK.rmdir()
                continue
            time.sleep(2)
            waited += 2
            if waited % 60 == 0:
                print(f"[leanlock] waiting for lean lock held by pid {pid} ({waited}s)", flush=True)
    try:
        yield
    finally:
        with contextlib.suppress(FileNotFoundError):
            (LOCK / "pid").unlink()
        with contextlib.suppress(OSError):
            LOCK.rmdir()
