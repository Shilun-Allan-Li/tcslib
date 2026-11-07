"""Run both gates' four copy-text screens serially under the screen lock.

Invoke with python3 -I after source-checks.py has made the immutable exports.
The unmodified outputs and the population of each run are gate evidence.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import time


def main() -> None:
    records = Path(__file__).resolve().parents[3]
    scratch = Path(os.environ["TCSLIB_SCRATCH"])
    lock = scratch / "locks/screen"
    while True:
        try:
            lock.mkdir()
            break
        except FileExistsError:
            time.sleep(5)
    (lock / "pid").write_text(str(os.getpid()) + "\n")
    try:
        cases = json.loads((scratch / "gate-source-exports/summary.json").read_text())
        for gate, data in cases.items():
            if os.environ.get("TCSLIB_SCREEN_GATE") not in (None, gate):
                continue
            evidence = records / "campaign/gates" / gate / "evidence/current/screen"
            labels = os.environ.get("TCSLIB_SCREEN_LABELS", "base,head").split(",")
            assert all(label in ("base", "head") for label in labels)
            for label in labels:
                population = (evidence / f"population-{label}.txt").read_text().splitlines()
                tree = data[f"{label}_export"]
                with (evidence / f"screen-{label}.txt").open("w") as output:
                    subprocess.run(
                        ["nice", "-n", "10", "python3", "-I",
                         str(records / "scripts/copy-text-screen-v3.py"), tree, *population],
                        stdout=output, stderr=subprocess.STDOUT, check=True,
                    )
                first = (evidence / f"screen-{label}.txt").read_text().splitlines()[0]
                (evidence / f"screen-{label}-commit.txt").write_text(data[label] + "\n")
                print(gate, label, first, flush=True)
            with (evidence / "pairdiff.txt").open("w") as output:
                subprocess.run(
                    ["python3", "-I", str(records / "devtools/seyoon/pairdiff.py"),
                     str(evidence / "screen-head.txt"), str(evidence / "screen-base.txt")],
                    stdout=output, stderr=subprocess.STDOUT, check=True,
                )
    finally:
        assert (lock / "pid").read_text().strip() == str(os.getpid())
        (lock / "pid").unlink()
        lock.rmdir()


if __name__ == "__main__":
    main()
