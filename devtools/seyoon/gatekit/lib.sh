# Sourced by the gate kit's shell scripts. Needs GATE (the gate's working folder, holding gate.json).
: "${GATE:?set GATE to the gate working folder (it holds gate.json)}"
KIT=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd); TOOLS=$(cd "$KIT/.." && pwd)
eval "$(python3 -I -c 'import json,os,shlex
c=json.load(open(os.path.join(os.environ["GATE"],"gate.json")))
for k in ("repo","scratch","head","base","input_snapshot","output_snapshot","records_gate"):
    print(k.upper()+"="+shlex.quote(str(c.get(k,""))))')"
export GATE KIT TOOLS REPO SCRATCH HEAD BASE INPUT_SNAPSHOT OUTPUT_SNAPSHOT RECORDS_GATE
export TCSLIB_SCRATCH="$SCRATCH" TCSLIB_REPO="$REPO"
[ -d "$HOME/.elan/bin" ] && export PATH="$HOME/.elan/bin:$PATH"
# Pool (workflow.md 4.1, Seyoon 2026-11-17): min(nproc, MemAvailable / 4 GB); the slot locks are the semaphore.
export TCSLIB_LEAN_SLOTS="${TCSLIB_LEAN_SLOTS:-$(bash "$TOOLS/leanpool.sh")}"
