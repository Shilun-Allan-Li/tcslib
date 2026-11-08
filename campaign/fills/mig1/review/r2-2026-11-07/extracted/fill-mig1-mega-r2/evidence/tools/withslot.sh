#!/usr/bin/env bash
# withslot.sh <cmd...>: run a command holding one of the TCSLIB_LEAN_SLOTS slot locks used by
# devtools/seyoon/leanelab.sh (same lock directory and protocol), so Lean processes never overlap.
LOCKS="${TCSLIB_SCRATCH:-$HOME/.tcslib-scratch}"/locks
SLOT_LIMIT="${TCSLIB_LEAN_SLOTS:-5}"
mkdir -p "$LOCKS"; SLOT=""
release() { if [ -n "$SLOT" ]; then rm -f "$SLOT/pid"; rmdir "$SLOT" 2>/dev/null; SLOT=""; fi; }
trap release EXIT; trap 'release; exit 130' INT TERM
while [ -z "$SLOT" ]; do
  for ((i=1; i<=SLOT_LIMIT; i++)); do
    s="$LOCKS/lean-slot-$i"
    if mkdir "$s" 2>/dev/null; then echo $$ > "$s/pid"; SLOT="$s"; break; fi
    p=$(cat "$s/pid" 2>/dev/null)
    if { [ -n "$p" ] && ! kill -0 "$p" 2>/dev/null; } || { [ -z "$p" ] && [ -n "$(find "$s" -maxdepth 0 -mmin +1 2>/dev/null)" ]; }; then
      rm -f "$s/pid"; rmdir "$s" 2>/dev/null
    fi
  done
  [ -z "$SLOT" ] && sleep 2
done
"$@"
