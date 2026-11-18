#!/usr/bin/env bash
# lean-slot.sh: run one command while holding host-wide Lean slots.
#
# Every Lean-running command on the host goes through this script: each
# scripts/lean_check_tree.sh call, each probe, and each `lake exe cache get`.
# The cap only holds if every job on the host uses the same slot directory.
#
#   lean-slot.sh [-k K] <command> [args...]
#
#   -k K  hold K slots (default 1). Use -k 3 for `lake exe cache get`, whose
#         Lake jobs can start several Lean processes at once.
#
# Environment variables:
#   LEAN_SLOT_DIR  the slot directory (default $HOME/.lean-slots), shared by all jobs
#   LEAN_SLOTS     the number of slots (default 3)
#   LEAN_SLOT_TAG  a label for the log (default: the current directory's name)
#
# Slots are directories created with mkdir, which is atomic on macOS and on
# Linux. Each slot directory holds the wrapper's PID. A slot whose PID is no
# longer alive is reaped by the next waiter. A slot with no PID file yet is
# left alone for 2 minutes, which covers the moment between mkdir and the
# PID write.
#
# A multi-slot request first takes the "big" lock. Only multi-slot requests
# use that lock. So two of them never hold part of a set each and wait on
# each other, and a single-slot request never waits on anything but slots.
# Works with bash 3.2 (the macOS default). The command's exit status is
# passed through.
set -u
DIR="${LEAN_SLOT_DIR:-$HOME/.lean-slots}"
N="${LEAN_SLOTS:-3}"
TAG="${LEAN_SLOT_TAG:-$(basename "$PWD")}"
K=1
if [ "${1:-}" = "-k" ]; then K="$2"; shift 2; fi
[ "$#" -ge 1 ] || { echo "usage: lean-slot.sh [-k K] command..." >&2; exit 2; }
[ "$K" -ge 1 ] && [ "$K" -le "$N" ] || { echo "lean-slot: -k must be 1..$N" >&2; exit 2; }
mkdir -p "$DIR"
HELD=""
BIG=""

log() { printf '%s %s pid=%s tag=%s %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$1" "$$" "$TAG" "$2" >> "$DIR/slots.log"; }

reap() { # $1 = lock directory; remove it if its owner is dead
  d="$1"
  [ -d "$d" ] || return 0
  if [ -f "$d/pid" ]; then
    p="$(cat "$d/pid" 2>/dev/null || true)"
    if [ -n "$p" ] && ! kill -0 "$p" 2>/dev/null; then
      rm -rf "$d" && log REAP "$(basename "$d") dead=$p"
    fi
  elif [ -n "$(find "$d" -maxdepth 0 -mmin +2 2>/dev/null)" ]; then
    rm -rf "$d" && log REAP "$(basename "$d") nopid"
  fi
}

take() { # $1 = lock directory; succeed only if this process created it
  if mkdir "$1" 2>/dev/null; then echo "$$" > "$1/pid"; return 0; fi
  return 1
}

release() {
  for d in $HELD; do rm -rf "$d"; done
  [ -n "$BIG" ] && rm -rf "$BIG"
  [ -n "$HELD" ] && log RELEASE "slots=[$(for d in $HELD; do printf '%s ' "$(basename "$d")"; done)]"
  HELD=""; BIG=""
}
trap release EXIT
trap 'release; exit 130' INT
trap 'release; exit 143' TERM

if [ "$K" -gt 1 ]; then
  until take "$DIR/big"; do reap "$DIR/big"; sleep 5; done
  BIG="$DIR/big"
fi
got=0
while [ "$got" -lt "$K" ]; do
  i=1
  while [ "$i" -le "$N" ] && [ "$got" -lt "$K" ]; do
    d="$DIR/slot$i"
    case " $HELD " in *" $d "*) i=$((i + 1)); continue ;; esac
    if take "$d"; then HELD="$HELD $d"; got=$((got + 1)); else reap "$d"; fi
    i=$((i + 1))
  done
  [ "$got" -lt "$K" ] && sleep 5
done
[ -n "$BIG" ] && rm -rf "$BIG" && BIG=""
log ACQUIRE "k=$K cmd=$*"
"$@"
rc=$?
release
exit "$rc"
