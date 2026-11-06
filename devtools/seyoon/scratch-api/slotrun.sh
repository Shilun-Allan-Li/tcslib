#!/usr/bin/env bash
# slotrun.sh <command…>: run a command that starts one Lean process at a time (a replay script,
# which calls scripts/lean_check_tree.sh and takes no slot itself) while holding one of the two
# machine-wide Lean slots ($TCSLIB_SCRATCH/locks/lean-slot-{1,2}, leanelab.sh's protocol), so the
# two-process limit holds. Waits silently for a free slot; releases it on exit.
. "${TCSLIB_SCRATCH:?set TCSLIB_SCRATCH}/env.sh"
LOCKS=$TCSLIB_SCRATCH/locks; mkdir -p "$LOCKS"; SLOT=""
release() { if [ -n "$SLOT" ]; then rm -f "$SLOT/pid"; rmdir "$SLOT" 2>/dev/null; SLOT=""; fi; }
trap release EXIT
trap 'release; exit 130' INT TERM
while [ -z "$SLOT" ]; do
  for i in 1 2; do
    s="$LOCKS/lean-slot-$i"
    if mkdir "$s" 2>/dev/null; then echo $$ > "$s/pid"; SLOT="$s"; break; fi
    p=$(cat "$s/pid" 2>/dev/null)
    if { [ -n "$p" ] && ! kill -0 "$p" 2>/dev/null; } || { [ -z "$p" ] && [ -n "$(find "$s" -maxdepth 0 -mmin +1 2>/dev/null)" ]; }; then
      rm -f "$s/pid"; rmdir "$s" 2>/dev/null
    fi
  done
  [ -z "$SLOT" ] && sleep 5
done
"$@"
