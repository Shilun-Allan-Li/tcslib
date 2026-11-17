#!/usr/bin/env bash
# memsample.sh <out> (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Seyoon's ruling of 2026-11-17 (workflow.md §4.1
# "Lean parallelism", PR #353) asks to record the pool size and peak memory. Every 30 s: UTC time, MemAvailable (kB), the
# number of running lean processes, and per process pid, anonymous kB and RSS kB (/proc/<pid>/smaps_rollup), and the probe.
while true; do
  t=$(date -u +%FT%TZ); a=$(awk '/MemAvailable/{print $2}' /proc/meminfo)
  ps=$(pgrep -f '^/root/.elan/toolchains/.*/bin/lean ')
  n=$(echo "$ps" | grep -c .)
  line="$t avail_kB=$a lean=$n"
  for p in $ps; do
    an=$(awk '/^Anonymous:/{print $2}' /proc/$p/smaps_rollup 2>/dev/null); rs=$(awk '/^Rss:/{print $2}' /proc/$p/smaps_rollup 2>/dev/null)
    f=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null | awk '{print $NF}')
    line="$line | $p anon=${an:-?} rss=${rs:-?} $f"
  done
  echo "$line" >> $1
  sleep 30
done
