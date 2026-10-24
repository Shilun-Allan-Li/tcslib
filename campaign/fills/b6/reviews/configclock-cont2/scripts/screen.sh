#!/usr/bin/env bash
# The one v3 screen run at the delivered head, niced, under the machine-wide screen lock.
# usage: screen.sh <root worktree> <population file> <out file>
ROOT="$1"; POP="$2"; OUT="$3"; LOCK=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen.lock
echo "waiting for the lock from $(date -u +%FT%TZ)" > "$OUT.status"
until mkdir "$LOCK" 2>/dev/null; do sleep 15; done
trap 'rmdir "$LOCK"' EXIT
echo "lock acquired $(date -u +%FT%TZ)" >> "$OUT.status"
cd "$ROOT" || exit 1
start=$(date +%s)
nice -n 10 python3 -I scripts/copy-text-screen-v3.py "$ROOT" $(cat "$POP") > "$OUT"
rc=$?
echo "exit $rc root $ROOT (HEAD $(git -C "$ROOT" rev-parse HEAD); tracked changes: $(git -C "$ROOT" status --short --untracked-files=no | tr '\n' ' ')) wall $(( $(date +%s) - start )) s, finished $(date -u +%FT%TZ)" >> "$OUT.status"
