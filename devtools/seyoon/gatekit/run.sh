#!/usr/bin/env bash
# One gate run on gate.json's head: prepare, replay, checks and sweeps, copy screen, citation homes,
# pair dispositions. Usage: GATE=<gate folder> bash run.sh. Move an earlier run aside first (runN/).
set -uo pipefail
source "$(dirname "$0")/lib.sh"
cd "$GATE" || exit 1
python3 -I "$KIT/prepare.py" || exit 1
python3 -I "$KIT/mksource.py" "$HEAD" "$BASE" "$GATE" || exit 1
python3 -I "$KIT/driver.py" "$GATE/driver-request.json" > "$GATE/replay.out" 2>&1 || { echo REPLAY-FAIL; tail -5 "$GATE/replay.out"; exit 1; }
tail -1 "$GATE/replay.out"
bash "$KIT/pipeline.sh" > "$GATE/pipeline.out" 2>&1
bash "$KIT/screen.sh" > "$GATE/screen.log" 2>&1
python3 -I "$KIT/defsweep/cites-summary.py" > "$GATE/defsweep/cites-summary.out" 2>&1
grep -E "^REPLAY |^COMPILED|^CONTROL|read candidates|^SEALS" "$GATE/checks.out"
grep "'operation'" "$GATE/checks.out" | cut -c1-220
grep -E "exit [1-9]" "$GATE/pipeline.out"
tail -1 "$GATE/screen/pairdiff.txt"
python3 -I "$KIT/dispositions.py"
echo "RUN DONE"
