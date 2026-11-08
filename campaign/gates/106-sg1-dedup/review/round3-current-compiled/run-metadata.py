"""One managed plain Lean process; stream full UTF-8 output losslessly to gzip/base64."""
from pathlib import Path
import base64
import codecs
import datetime
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
import time

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
context = json.loads((OUT / "context.json").read_text())
label, version = sys.argv[1:]
assert label in {"Base", "Head"}
if label == "Head":
    authorization = json.loads((OUT / "HEAD-REPLAY-PASS.json").read_text())
    assert authorization["head"] == context["head"] and authorization["root_authorized_readonly_probe"]
snapshot = Path(context["base_snapshot"] if label == "Base" else context["head_snapshot"])
stem = label + "-" + version
receipt_path = OUT / (stem + "-run.json")
raw_record = OUT / (stem + ".out.gz.b64")
assert not receipt_path.exists() and not raw_record.exists()
source = OUT / ("Metadata-" + version + ".lean.txt")
data = source.read_bytes()
scratch = Path(context["scratch"])
actual = scratch / (stem + ".lean")
actual.write_bytes(data)
command = ["bash", str(ROOT / "devtools/seyoon/leanelab.sh"), context["worktree"], str(snapshot), str(actual)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def owner_artifacts():
    result = {}
    for owner in (OUT / "original9-owners.txt").read_text().splitlines():
        rel = owner.replace(".", "/") + ".olean"
        path = snapshot / rel
        result[rel] = dict(bytes=path.stat().st_size, sha256=sha(path))
    return result


before = owner_artifacts()
request = dict(command=command, start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               input_sha256=hashlib.sha256(data).hexdigest(), snapshot=str(snapshot),
               context_commit=context["base"] if label == "Base" else context["head"],
               local_budget=os.environ.get("TCSLIB_LEAN_SLOTS"), max_own_Lean_processes=1,
               plain_managed=True, no_compiled_output=True, owner_artifacts_before=before,
               stdout_format="Full lossless UTF-8, deterministic gzip, base64 ASCII; no output cap")
(OUT / (stem + "-request.json")).write_text(json.dumps(request, indent=2) + "\n")
start = time.monotonic()
gz_path = scratch / (stem + ".out.gz")
digest = hashlib.sha256()
decoder = codecs.getincrementaldecoder("utf-8")("strict")
total = 0
proc = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert proc.stdout is not None
with gz_path.open("wb") as sink:
    with gzip.GzipFile(fileobj=sink, filename="", mode="wb", mtime=0) as compressed:
        while True:
            chunk = proc.stdout.read(1024 * 1024)
            if not chunk:
                break
            decoder.decode(chunk)
            total += len(chunk)
            digest.update(chunk)
            compressed.write(chunk)
decoder.decode(b"", final=True)
exit_code = proc.wait()
with gz_path.open("rb") as source_gz, raw_record.open("wb") as encoded:
    base64.encode(source_gz, encoded)
errors = warnings = lines = 0
verified = hashlib.sha256()
with gzip.open(gz_path, "rb") as restored:
    for line in restored:
        verified.update(line)
        lines += 1
        errors += bool(re.search(rb"^[^|\n]*:\d+:\d+: error(?:\([^)]*\))?:", line))
        warnings += bool(re.search(rb"^[^|\n]*:\d+:\d+: warning:", line))
assert verified.hexdigest() == digest.hexdigest()
after = owner_artifacts()
assert before == after, "Read-only imported owner artifacts changed"
request.update(exit=exit_code, seconds=time.monotonic()-start, errors=errors, warnings=warnings,
               raw_utf8_bytes=total, raw_utf8_lines=lines, raw_utf8_sha256=digest.hexdigest(),
               gzip_bytes=gz_path.stat().st_size, gzip_sha256=sha(gz_path),
               base64_bytes=raw_record.stat().st_size, base64_sha256=sha(raw_record),
               lossless_decompression_hash_verified=True, owner_artifacts_unchanged=True,
               input_still_exact=sha(source) == hashlib.sha256(data).hexdigest())
receipt_path.write_text(json.dumps(request, indent=2) + "\n")
print(json.dumps({k: request[k] for k in ["exit", "seconds", "errors", "warnings", "raw_utf8_bytes", "raw_utf8_lines", "raw_utf8_sha256", "base64_bytes", "owner_artifacts_unchanged"]}, indent=2))
if exit_code:
    with gzip.open(gz_path, "rt", encoding="utf-8") as restored:
        for line in restored:
            if re.search(r"^[^|\n]*:\d+:\d+: error(?:\([^)]*\))?:", line):
                print(line.rstrip())
