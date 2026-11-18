#!/usr/bin/env bash
# rule10_regev.sh <evidence-dir> <head-rev> <owners> <phase>...
#
# ORIGIN / ADAPTATIONS (tools-agent, sub-agent of fill ef-r23-regev, 2026-11-18). Merges
# /home/user/ef-r23/tools/bb1m-tools/drivers/rule10_final.sh (phases collect / pretest / seals) and
# /home/user/ef-r23/tools/bb1m-tools/seal/rule10_b.sh (the seals body). Adaptations:
#  (1) host paths: repository W=/home/user/ef-r23/repo (git objects only: `git show <head>:<path>`), olean tree
#      TREE=$TCSLIB_OLEANS (default /home/user/ef-r23/oleans), lake packages $LAKE_PACKAGES (default
#      $W/.lake/packages), evidence dir E = argument 1 (e.g. /home/user/ef-r23/evidence/rule10-<tag>);
#  (2) probes are written OUTSIDE the repository, under PROBES=${PROBE_ROOT:-/home/user/ef-r23/probes/<basename E>}
#      (absolute <probe-subdir>, see mkctl_regev.py adaptation 5); nothing is written into $W or $TREE;
#  (3) owners: argument 3 is a file of dotted module names (one per line, # comments allowed) or a
#      comma-separated list; series 1+2 file: owners-s12.txt next to this script;
#  (4) the single-host `flock` lock is gone: seal/runner_regev.py runs at most $RULE10_JOBS (default 2) Lean
#      processes at once (lean -DmaxErrors=0, no -o); every phase is separately invocable;
#  (5) `collect` only GENERATES the collector and PRINTS the exact commands (runner and bare lean); the lead runs
#      it, or runs phase `collect-run`; `collect-check` verifies the collector log (one CLOSURE and one MODULE
#      line per owner, a CAT-COUNT line, no error line);
#  (6) the controls generator is mkctl_regev.py (rows in control-rows.tsv, env CTL_ROWS overrides);
#  (7) `seals` first writes $E/statements/touched-after.json with touched.py (base = IO base 5ed465f6..., head =
#      <head-rev>, files = the owners' sources) because sealsum.py maps errors to declarations through it;
#  (8) `pretest` keeps bb1m's shape (coe seal A -> controls -> unsealed ControlU_* only) and also checks them
#      with ctlcheck2.py on the unsealed half of the plan; it does not delete the probes (they are outside W);
#  (9) DRY=1 makes every runner call print its commands instead of running Lean (no records written).
# Phases (any order on the command line, run left to right):
#   collect        write $PROBES/CollectHead.lean (mkcollect.py + NmCollect.template.lean) and print commands
#   collect-run    run the collector through runner_regev.py  -> $E/rule10/probe-runs
#   collect-check  sanity-check the collector log
#   pretest        unsealed controls only                     -> $E/rule10/pretest
#   seals          strict + coe seals A/B, paired controls, one runner pass, sealsum + ctlcheck2 -> $E/rule10
#   print-env      print LEAN_PATH and paths
set -u
[ $# -ge 4 ] || { sed -n '2,32p' "$0"; exit 2; }
E=$(realpath -m "$1"); H_IN=$2; OWN=$3; shift 3
HERE=$(cd "$(dirname "$0")" && pwd)
T=$HERE/seal; G=$T/review/archived-gate10-tools; CTL=$HERE/mkctl_regev.py
W=${REPO:-/home/user/ef-r23/repo}
TREE=${TCSLIB_OLEANS:-/home/user/ef-r23/oleans}
export LAKE_PACKAGES=${LAKE_PACKAGES:-$W/.lake/packages}
export RULE10_JOBS=${RULE10_JOBS:-2}
BASE=5ed465f62e4ae0f93ded1a1ba49e807591b589eb
H=$(git -C "$W" rev-parse --verify "$H_IN^{commit}") || { echo "bad head rev $H_IN"; exit 2; }
PROBES=${PROBE_ROOT:-/home/user/ef-r23/probes/$(basename "$E")}
R=$E/rule10
OWNP=$OWN; [ -f "$OWN" ] && OWNP=$(realpath "$OWN")
if [ -f "$OWN" ]; then MODS=$(grep -v '^\s*#' "$OWN" | tr -s ' \t' '\n' | grep -v '^$'); else MODS=$(echo "$OWN" | tr ',' '\n' | grep -v '^$'); fi
MODS=$(echo $MODS)
[ -n "$MODS" ] || { echo "no owners"; exit 2; }
for m in $MODS; do git -C "$W" cat-file -e "$H:$(echo $m | tr . /).lean" 2>/dev/null || { echo "owner $m: no source at $H"; exit 2; }; done
LP="$TREE"; for d in "$LAKE_PACKAGES"/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
PY="python3 -I"
CLOG=$R/probe-runs/mods/$(echo "$PROBES/CollectHead" | tr / _).log
mkdir -p "$R/order" "$R/probe-sources" "$PROBES"
runner() { $PY "$T/runner_regev.py" "$W" "$@"; }
for ph in "$@"; do
echo "phase $ph start $(date -u +%FT%TZ) head $H owners $MODS jobs $RULE10_JOBS"
case $ph in
print-env)
  echo "W=$W"; echo "TREE=$TREE"; echo "PROBES=$PROBES"; echo "E=$E"; echo "LEAN_PATH=$LP"; echo "collector log: $CLOG";;
collect)
  printf '%s\n' $MODS > "$R/order/owners.txt"
  $PY "$T/review/mkcollect.py" "$T/review/NmCollect.template.lean" "$R/order/owners.txt" \
    "fill ef-r23-regev collector (head $H)" "$PROBES/CollectHead.lean" || exit 1
  cp "$PROBES/CollectHead.lean" "$R/probe-sources/CollectHead.lean.txt"
  printf '%s\n' "$PROBES/CollectHead" > "$R/order/probes.txt"
  echo "collector: $PROBES/CollectHead.lean (sha256 $(sha256sum < "$PROBES/CollectHead.lean" | cut -c1-64))"
  echo "RUN EITHER (preferred, writes results.jsonl):"
  echo "  bash $HERE/$(basename "$0") $E $H $OWNP collect-run"
  echo "OR the bare command (log must land at the path below for phases pretest/seals):"
  echo "  mkdir -p $R/probe-runs/mods && cd $W && env PATH=\$HOME/.elan/bin:\$PATH LEAN_PATH=$LP nice -n 10 lean -DmaxErrors=0 $PROBES/CollectHead.lean > $CLOG 2>&1";;
collect-run)
  runner "$R/order/probes.txt" "$TREE" "$R/probe-runs" > "$R/probe-runner.out" 2>&1; echo "collector rc=$?"; cat "$R/probe-runner.out";;
collect-check)
  [ -f "$CLOG" ] || { echo "no collector log $CLOG"; exit 1; }
  ok=1
  for m in $MODS; do
    # lead fix (2026-11-18): compressed JSON orders keys, so "closure" precedes "module"
    c=$(grep -c "^CLOSURE {.*\"module\":\"$m\"}" "$CLOG"); s=$(grep -c "^MODULE $m: stored " "$CLOG")
    echo "owner $m CLOSURE=$c MODULE=$s $(grep "^MODULE $m: stored " "$CLOG")"; [ "$c" = 1 ] && [ "$s" = 1 ] || ok=0
  done
  grep -m1 '^CAT-COUNT ' "$CLOG" || ok=0
  e=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error' "$CLOG"); echo "error lines: $e"; [ "$e" = 0 ] || ok=0
  echo "COLLECT_OK $ok"; [ $ok = 1 ] || exit 1;;
pretest)
  Q=$R/pretest; mkdir -p "$Q/seals-flat"
  $PY "$T/review/mkseals_coe.py" "$G" "$CLOG" "$W" "$H" "$Q/seals-coe/A" "$PROBES/QC" SealA_ $MODS > "$Q/mkseals-coe-A.log" || { cat "$Q/mkseals-coe-A.log"; exit 1; }
  cp "$Q"/seals-coe/A/Seal*.json "$Q/seals-flat/"
  $PY "$CTL" "$G" "$Q/seals-flat" "$W" "$PROBES/QK" "$Q/controls" > "$Q/mkctl.log" || { cat "$Q/mkctl.log"; exit 1; }
  ls "$PROBES"/QK/ControlU_*.lean | sed 's/\.lean$//' | LC_ALL=C sort > "$Q/order.txt"
  runner "$Q/order.txt" "$TREE" "$Q/runs" > "$Q/runner.out" 2>&1
  if [ "${DRY:-0}" = 1 ]; then cat "$Q/runner.out"; else
  grep -h '"module"' "$Q/runs/results.jsonl" | $PY -c "import sys,json;[print(r['module'],r['rc'],r['errors']) for r in map(json.loads,sys.stdin)]" | tee "$Q/summary.txt"
  $PY -c "import json,sys;p=json.load(open(sys.argv[1]));json.dump([x for x in p if not x['sealed']],open(sys.argv[2],'w'),indent=1)" "$Q/controls/controls-plan.json" "$Q/controls/plan-unsealed.json"
  $PY "$T/review/ctlcheck2.py" "$Q/controls/plan-unsealed.json" "$Q/runs" "$Q/ctlcheck-unsealed.json" | tee "$Q/ctlcheck-unsealed.log"; fi
  cat "$Q/mkctl.log";;
seals)
  mkdir -p "$E/statements"
  FILES=$(for m in $MODS; do echo "$(echo $m | tr . /).lean"; done)
  $PY "$T/review/touched.py" "$W" "$BASE" "$H" "$E/statements/touched-after.json" $FILES > "$E/statements/touched-after.tsv" || exit 1
  set -e
  $PY "$T/review/mkseals_ab.py" "$G" "$CLOG" "$W" "$H" "$R/seals/A" "$PROBES/S" SealA_ $MODS > "$R/mkseals-A.log"
  SEAL_EVAL=1 $PY "$T/review/mkseals_ab.py" "$G" "$CLOG" "$W" "$H" "$R/seals/B" "$PROBES/S" SealB_ $MODS > "$R/mkseals-B.log"
  $PY "$T/review/mkseals_coe.py" "$G" "$CLOG" "$W" "$H" "$R/seals-coe/A" "$PROBES/C" SealA_ $MODS > "$R/mkseals-coe-A.log"
  SEAL_EVAL=1 $PY "$T/review/mkseals_coe.py" "$G" "$CLOG" "$W" "$H" "$R/seals-coe/B" "$PROBES/C" SealB_ $MODS > "$R/mkseals-coe-B.log"
  mkdir -p "$R/seals-flat" "$R/seals-coe-flat"
  for v in A B; do
    for f in "$R"/seals/$v/Seal*.json; do cp "$f" "$R/seals-flat/"; done
    for f in "$R"/seals-coe/$v/Seal*.json; do cp "$f" "$R/seals-coe-flat/"; done
  done
  $PY "$CTL" "$G" "$R/seals-flat" "$W" "$PROBES/KS" "$R/controls-strict" > "$R/mkctl-strict.log"
  $PY "$CTL" "$G" "$R/seals-coe-flat" "$W" "$PROBES/K" "$R/controls-coe" > "$R/mkctl-coe.log"
  set +e
  ls "$PROBES"/C/*.lean "$PROBES"/K/*.lean "$PROBES"/KS/*.lean "$PROBES"/S/*.lean 2>/dev/null | sed 's/\.lean$//' | LC_ALL=C sort > "$R/order/seal-control-queue.txt"
  runner "$R/order/seal-control-queue.txt" "$TREE" "$R/seal-runs" > "$R/seal-runner.out" 2>&1
  if [ "${DRY:-0}" = 1 ]; then cat "$R/seal-runner.out"; cat "$R"/mkseals-*.log "$R"/mkctl-*.log; else
  TJ=$E/statements/touched-after.json
  for v in seals/A seals/B seals-coe/A seals-coe/B; do
    $PY "$T/review/sealsum.py" "$R/$v" "$R/seal-runs" "$TJ" "$R/$(echo $v | tr / -).tsv"; done
  $PY "$T/review/ctlcheck2.py" "$R/controls-strict/controls-plan.json" "$R/seal-runs" "$R/ctlcheck-strict.json" > "$R/ctlcheck-strict.log"
  $PY "$T/review/ctlcheck2.py" "$R/controls-coe/controls-plan.json" "$R/seal-runs" "$R/ctlcheck-coe.json" > "$R/ctlcheck-coe.log"
  cat "$R"/mkseals-*.log "$R"/mkctl-*.log; cat "$R"/seals-*.tsv; for f in "$R/ctlcheck-strict.log" "$R/ctlcheck-coe.log"; do tail -n 1 "$f"; done; fi;;
*) echo "unknown phase $ph"; exit 2;;
esac
echo "phase $ph done $(date -u +%FT%TZ)"
done
