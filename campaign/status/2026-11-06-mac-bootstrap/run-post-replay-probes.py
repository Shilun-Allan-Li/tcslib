"""Run final imported-module checks after each corresponding replay passes."""

from pathlib import Path
import os
import re
import subprocess
import time


scratch = Path(os.environ["TCSLIB_SCRATCH"])
records = Path(__file__).resolve().parents[3]
runner = Path(__file__).with_name("run-probes.py")
for name, gate, wt, count, probes in [
    ("msg1", "106-sg1-dedup", "wt-sg1", 329,
     ["axioms/Axioms.lean.txt:0", "axioms/ModuleCensus-head.lean.txt:0"]),
    ("mnb1", "114-natbits-dedup", "wt-natbits", 344,
     ["axioms/Axioms.lean.txt:0", "axioms/ModuleCensus-head.lean.txt:0",
      "Sanity.lean.txt:0", "seal/FragCell.lean.txt:0"]),
]:
    log = scratch / "fills/replay" / ("replay-" + name + ".log")
    while True:
        lines = log.read_text().splitlines() if log.exists() else []
        if lines and re.fullmatch(r"# modules=\d+ failed=\d+", lines[-1]):
            assert lines[-1] == f"# modules={count} failed=0", lines[-1]
            static = log.with_name(log.stem + "-static.txt")
            if static.exists() and "mismatches 0," in static.read_text():
                break
        time.sleep(10)
    subprocess.run(
        ["python3", "-I", str(runner), gate, wt, "oleans-" + name, *probes],
        cwd=records, check=True)
