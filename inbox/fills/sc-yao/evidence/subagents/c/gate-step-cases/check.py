from pathlib import Path
import subprocess, os, datetime, re, json, sys
module = sys.argv[1]
label = sys.argv[2]
base = Path("evidence/subagents/c/gate-step-cases")
log = base / (label + ".log")
(base / (label + ".source.lean")).write_bytes(Path(module + ".lean").read_bytes())
env = os.environ.copy()
env["LEAN_SLOT_TAG"] = "sc-yao-c"
env["TCSLIB_OLEANS"] = str(Path(".lake/sc-yao-oleans").resolve())
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
with log.open("w") as stream:
    stream.write("START " + start + "\n")
    stream.flush()
    result = subprocess.run([
        "/private/tmp/sc-yao-lean-slot.sh", "/usr/bin/time", "-l", "bash",
        "scripts/lean_check_tree.sh", module
    ], env=env, stdout=stream, stderr=subprocess.STDOUT, text=True)
    stream.write("END " + datetime.datetime.now(datetime.timezone.utc).isoformat()
                 + f" exit={result.returncode}\n")
raw = log.read_text()
errors = len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", raw, re.M))
record = {"module": module, "log": str(log), "exit": result.returncode,
          "errors": errors, "start": start}
with (base / "results.jsonl").open("a") as stream:
    stream.write(json.dumps(record) + "\n")
print(raw)
print(record)
sys.exit(result.returncode or int(errors != 0))
