"""Sequential native macOS bootstrap; run from the campaign root with python3 -I."""

from pathlib import Path
import datetime
import hashlib
import os
import re
import subprocess
import sys
import time


root = Path.cwd()
out = root / "briefs/pass-shelat-ch5-8/maintainer/environment-2026-11-06"
logs = out / "evidence/logs"
modules = (out / "order.txt").read_text().splitlines()
base = (out / "BASE.txt").read_text().strip()
env = os.environ.copy()
env["TCSLIB_OLEANS"] = str(root / ".lake/ps-maintainer/oleans-base")


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


fingerprints = []
for module in modules:
    path = module + ".lean"
    expected = subprocess.check_output(["git", "show", base + ":" + path])
    actual = (root / path).read_bytes()
    assert actual == expected, "source differs from pinned base: " + path
    fingerprints.append(hashlib.sha256(actual).hexdigest() + "  " + path)
(out / "source-sha256.txt").write_text("\n".join(fingerprints) + "\n")

with (logs / "bootstrap.log").open("w") as summary:
    def record(line):
        summary.write(line + "\n")
        summary.flush()
        print(line, flush=True)

    record("START " + now() + " BASE " + base)
    record("TCSLIB_OLEANS " + env["TCSLIB_OLEANS"])
    for index, module in enumerate(modules, 1):
        log = logs / "modules" / (module + ".log")
        log.parent.mkdir(parents=True, exist_ok=True)
        start = now()
        elapsed = time.monotonic()
        with log.open("w") as handle:
            handle.write("START " + start + "\n")
            handle.flush()
            process = subprocess.Popen(
                ["/usr/bin/time", "-l", "bash", "scripts/lean_check_tree.sh", module],
                stdout=handle,
                stderr=subprocess.STDOUT,
                env=env,
            )
            (logs / "bootstrap.pid").write_text(str(process.pid) + "\n")
            rc = process.wait()
            end = now()
            elapsed = time.monotonic() - elapsed
            handle.write("\nEND " + end + " RC " + str(rc) + "\n")
        text = log.read_text()
        rss = re.search(r"(\d+)\s+maximum resident set size", text)
        record(
            f"{index}/{len(modules)} {module} rc={rc} "
            f"elapsed={elapsed:.3f}s rss_bytes={rss.group(1) if rss else 'unavailable'} "
            f"start={start} end={end}"
        )
        if rc:
            record("STOP at " + module + "; prerequisites for later checks are unavailable")
            sys.exit(rc)
    record("DONE " + now())
