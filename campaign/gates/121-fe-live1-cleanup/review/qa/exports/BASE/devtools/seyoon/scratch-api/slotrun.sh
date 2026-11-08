#!/usr/bin/env bash
# slotrun.sh <command…>: run a command that starts one Lean process at a time (a replay script,
# which calls scripts/lean_check_tree.sh and takes no slot itself) while holding a Lean slot.
# The machine-wide cap is five (user, 2026-11-06); TCSLIB_LEAN_SLOTS may set a smaller local
# budget for another campaign's separate locks. Waits silently; releases the slot on exit.
. "${TCSLIB_SCRATCH:?set TCSLIB_SCRATCH}/env.sh"
LOCKS=$TCSLIB_SCRATCH/locks; mkdir -p "$LOCKS"; SLOT=""
SLOT_LIMIT="${TCSLIB_LEAN_SLOTS:-5}"
case "$SLOT_LIMIT" in 1|2|3|4|5) ;; *) echo 'TCSLIB_LEAN_SLOTS must be 1..5' >&2; exit 2 ;; esac
release() { if [ -n "$SLOT" ]; then rm -f "$SLOT/pid"; rmdir "$SLOT" 2>/dev/null; SLOT=""; fi; }
trap release EXIT
trap 'release; exit 130' INT TERM
while [ -z "$SLOT" ]; do
  for ((i=1; i<=SLOT_LIMIT; i++)); do
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
