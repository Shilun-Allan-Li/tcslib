#!/usr/bin/env bash
# Lean pool size (workflow.md 4.1, Seyoon 2026-11-17): min(nproc, MemAvailable / 4 GB), at least 1.
a=$(awk '/^MemAvailable:/{print int($2/4194304)}' /proc/meminfo); n=$(nproc)
p=$(( a < n ? a : n )); [ "$p" -ge 1 ] || p=1
# The approved wrappers accept at most 5 slots.
[ "$p" -le 5 ] || p=5; echo "$p"
