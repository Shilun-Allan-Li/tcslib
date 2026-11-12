#!/usr/bin/env bash
# Elaborate one module file of worktree $1 against olean tree $2 (no olean output, nothing removed).
# Throttled (user, 2026-11-06): at most 5 elaborations machine-wide. TCSLIB_LEAN_SLOTS may
# reserve a smaller local budget while another campaign uses separate locks. Each has 4 threads.
# Waiting is silent; the output and exit status are lean's.
WT="$1"; OL="$2"; F="$3"; LP="$OL"
for d in "$WT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"
LOCKS="${TCSLIB_SCRATCH:-$HOME/.tcslib-scratch}"/locks
SLOT_LIMIT="${TCSLIB_LEAN_SLOTS:-5}"
case "$SLOT_LIMIT" in 1|2|3|4|5) ;; *) echo 'TCSLIB_LEAN_SLOTS must be 1..5' >&2; exit 2 ;; esac
mkdir -p "$LOCKS"
SLOT=""
release() { if [ -n "$SLOT" ]; then rm -f "$SLOT/pid"; rmdir "$SLOT" 2>/dev/null; SLOT=""; fi; }
trap release EXIT
trap 'release; exit 130' INT TERM
while [ -z "$SLOT" ]; do
  for ((i=1; i<=SLOT_LIMIT; i++)); do
    s="$LOCKS/lean-slot-$i"
    if mkdir "$s" 2>/dev/null; then echo $$ > "$s/pid"; SLOT="$s"; break; fi
    p=$(cat "$s/pid" 2>/dev/null)
    # reclaim a stale slot: its holder is gone, or it never recorded a pid within a minute
    if { [ -n "$p" ] && ! kill -0 "$p" 2>/dev/null; } || { [ -z "$p" ] && [ -n "$(find "$s" -maxdepth 0 -mmin +1 2>/dev/null)" ]; }; then
      rm -f "$s/pid"; rmdir "$s" 2>/dev/null
    fi
  done
  [ -z "$SLOT" ] && sleep 2
done
cd "$WT" || exit 1
nice -n 10 lean -j4 "$F"
