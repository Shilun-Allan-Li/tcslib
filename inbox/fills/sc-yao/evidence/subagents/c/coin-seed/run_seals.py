from pathlib import Path
import subprocess, os, datetime, re, json, fcntl
base = Path("evidence/subagents/c/coin-seed/seals")
lock = Path(".lake/sc-yao-c-seals.lock").open("a+")
fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
env = os.environ.copy()
env["LEAN_SLOT_TAG"] = "sc-yao-c"
env["TCSLIB_OLEANS"] = str(Path(".lake/sc-yao-oleans").resolve())
for phase in ["final"]:
    rows = json.loads((base / phase / "manifest.json").read_text())
    for row in rows:
        source = Path(row["probe"])
        module = str(source.with_suffix(""))
        log = source.with_suffix(".log")
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print("START", source.name, start, flush=True)
        with log.open("w") as stream:
            stream.write("START " + start + "\n")
            stream.flush()
            result = subprocess.run([
                "/private/tmp/sc-yao-lean-slot.sh", "/usr/bin/time", "-l", "bash",
                "evidence/subagents/c/check_seal.sh", module
            ], env=env, stdout=stream, stderr=subprocess.STDOUT)
            stream.write("END " + datetime.datetime.now(datetime.timezone.utc).isoformat()
                         + f" exit={result.returncode}\n")
        raw = log.read_text()
        errors = len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", raw, re.M))
        record = dict(row, log=str(log), exit=result.returncode, errors=errors,
                      start=start, phase=phase)
        with (base / "results.jsonl").open("a") as stream:
            stream.write(json.dumps(record) + "\n")
        print("END", source.name, "exit", result.returncode, "errors", errors, flush=True)
