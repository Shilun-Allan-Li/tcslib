#!/usr/bin/env bash
set -u
module="$1"
log="$2"
cp "$module.lean" "${log%.log}.source.lean"
{
  printf 'START %s module=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$module"
  LEAN_SLOT_TAG=sc-yao-a \
    TCSLIB_OLEANS=/Users/seyoonr/.codex/worktrees/sc-yao-a/tcslib-exchange/.lake/sc-yao-oleans \
    /private/tmp/sc-yao-lean-slot.sh /usr/bin/time -l \
      bash scripts/lean_check_tree.sh "$module"
  status=$?
  printf 'END %s status=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$status"
} > "$log" 2>&1
python3 -I evidence/subagents/a/summarize-log.py "$module" "$log" "$status"
exit "$status"
